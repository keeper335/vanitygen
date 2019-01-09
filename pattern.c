/*
 * Vanitygen, vanity bitcoin address generator
 * Copyright (C) 2011 <samr7@cs.washington.edu>
 *
 * Vanitygen is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * any later version. 
 *
 * Vanitygen is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 *
 * You should have received a copy of the GNU Affero General Public License
 * along with Vanitygen.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "pattern.h"
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <assert.h>

#include <pthread.h>

#include <openssl/sha.h>
#include <openssl/ripemd.h>
#include <openssl/bn.h>
#include <openssl/ec.h>
#include <openssl/obj_mac.h>

#include "util.h"


int str_cmp(const unsigned char * a, const unsigned char * b, int len) {
    for (int i=0; i < len; i++) {
        if (a[i]<b[i]) {
#ifdef DEBUG_PREFIXES
            printf("%02x less than %02x\n", a[i], b[i] );
#endif
            return -1;
        }
        else if (a[i]>b[i]) {
#ifdef DEBUG_PREFIXES
            printf("%02x more than %02x\n", a[i], b[i] );
#endif
            return 1;
        }
    }
    return 0;
}

/*
 * Common code for execution helper
 */

EC_KEY *
vg_exec_context_new_key(void)
{
	return EC_KEY_new_by_curve_name(NID_secp256k1);
}

/*
 * Thread synchronization helpers
 */

static pthread_mutex_t vg_thread_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t vg_thread_rdcond = PTHREAD_COND_INITIALIZER;
static pthread_cond_t vg_thread_wrcond = PTHREAD_COND_INITIALIZER;
static pthread_cond_t vg_thread_upcond = PTHREAD_COND_INITIALIZER;

static void
__vg_exec_context_yield(vg_exec_context_t *vxcp)
{
	vxcp->vxc_lockmode = 0;
	while (vxcp->vxc_vc->vc_thread_excl) {
		if (vxcp->vxc_stop) {
			assert(vxcp->vxc_vc->vc_thread_excl);
			vxcp->vxc_stop = 0;
			pthread_cond_signal(&vg_thread_upcond);
		}
		pthread_cond_wait(&vg_thread_rdcond, &vg_thread_lock);
	}
	assert(!vxcp->vxc_stop);
	assert(!vxcp->vxc_lockmode);
	vxcp->vxc_lockmode = 1;
}

int
vg_exec_context_upgrade_lock(vg_exec_context_t *vxcp)
{
	vg_exec_context_t *tp;
	vg_context_t *vcp;

	if (vxcp->vxc_lockmode == 2)
		return 0;

	pthread_mutex_lock(&vg_thread_lock);

	assert(vxcp->vxc_lockmode == 1);
	vxcp->vxc_lockmode = 0;
	vcp = vxcp->vxc_vc;

	if (vcp->vc_thread_excl++) {
		assert(vxcp->vxc_stop);
		vxcp->vxc_stop = 0;
		pthread_cond_signal(&vg_thread_upcond);
		pthread_cond_wait(&vg_thread_wrcond, &vg_thread_lock);

		for (tp = vcp->vc_threads; tp != NULL; tp = tp->vxc_next) {
			assert(!tp->vxc_lockmode);
			assert(!tp->vxc_stop);
		}

	} else {
		for (tp = vcp->vc_threads; tp != NULL; tp = tp->vxc_next) {
			if (tp->vxc_lockmode) {
				assert(tp->vxc_lockmode != 2);
				tp->vxc_stop = 1;
			}
		}

		do {
			for (tp = vcp->vc_threads;
			     tp != NULL;
			     tp = tp->vxc_next) {
				if (tp->vxc_lockmode) {
					assert(tp->vxc_lockmode != 2);
					pthread_cond_wait(&vg_thread_upcond,
							  &vg_thread_lock);
					break;
				}
			}
		} while (tp);
	}

	vxcp->vxc_lockmode = 2;
	pthread_mutex_unlock(&vg_thread_lock);
	return 1;
}

void
vg_exec_context_downgrade_lock(vg_exec_context_t *vxcp)
{
	pthread_mutex_lock(&vg_thread_lock);
	assert(vxcp->vxc_lockmode == 2);
	assert(!vxcp->vxc_stop);
	if (!--vxcp->vxc_vc->vc_thread_excl) {
		vxcp->vxc_lockmode = 1;
		pthread_cond_broadcast(&vg_thread_rdcond);
		pthread_mutex_unlock(&vg_thread_lock);
		return;
	}
	pthread_cond_signal(&vg_thread_wrcond);
	__vg_exec_context_yield(vxcp);
	pthread_mutex_unlock(&vg_thread_lock);
}

int
vg_exec_context_init(vg_context_t *vcp, vg_exec_context_t *vxcp)
{
	pthread_mutex_lock(&vg_thread_lock);

	memset(vxcp, 0, sizeof(*vxcp));

	vxcp->vxc_vc = vcp;

	BN_init(&vxcp->vxc_bntarg);
	BN_init(&vxcp->vxc_bnbase);
	BN_init(&vxcp->vxc_bntmp);
	BN_init(&vxcp->vxc_bntmp2);

	BN_set_word(&vxcp->vxc_bnbase, 58);

	vxcp->vxc_bnctx = BN_CTX_new();
	assert(vxcp->vxc_bnctx);
	vxcp->vxc_key = vg_exec_context_new_key();
	assert(vxcp->vxc_key);
	EC_KEY_precompute_mult(vxcp->vxc_key, vxcp->vxc_bnctx);

	vxcp->vxc_lockmode = 0;
	vxcp->vxc_stop = 0;

	vxcp->vxc_next = vcp->vc_threads;
	vcp->vc_threads = vxcp;
	vxcp->vc_combined_compressed = vcp->vc_compressed;
	__vg_exec_context_yield(vxcp);
	pthread_mutex_unlock(&vg_thread_lock);
	return 1;
}

void
vg_exec_context_del(vg_exec_context_t *vxcp)
{
	printf("vg_exec_context_del\n");
	
	vg_exec_context_t *tp, **pprev;

	if (vxcp->vxc_lockmode == 2)
		vg_exec_context_downgrade_lock(vxcp);

	pthread_mutex_lock(&vg_thread_lock);
	assert(vxcp->vxc_lockmode == 1);
	vxcp->vxc_lockmode = 0;

	for (pprev = &vxcp->vxc_vc->vc_threads, tp = *pprev;
	     (tp != vxcp) && (tp != NULL);
	     pprev = &tp->vxc_next, tp = *pprev);

	assert(tp == vxcp);
	*pprev = tp->vxc_next;

	if (tp->vxc_stop)
		pthread_cond_signal(&vg_thread_upcond);

	BN_clear_free(&vxcp->vxc_bntarg);
	BN_clear_free(&vxcp->vxc_bnbase);
	BN_clear_free(&vxcp->vxc_bntmp);
	BN_clear_free(&vxcp->vxc_bntmp2);
	BN_CTX_free(vxcp->vxc_bnctx);
	vxcp->vxc_bnctx = NULL;
	pthread_mutex_unlock(&vg_thread_lock);
}

void
vg_exec_context_yield(vg_exec_context_t *vxcp)
{
	if (vxcp->vxc_lockmode == 2)
		vg_exec_context_downgrade_lock(vxcp);

	else if (vxcp->vxc_stop) {
		assert(vxcp->vxc_lockmode == 1);
		pthread_mutex_lock(&vg_thread_lock);
		__vg_exec_context_yield(vxcp);
		pthread_mutex_unlock(&vg_thread_lock);
	}

	assert(vxcp->vxc_lockmode == 1);
}

void
vg_exec_context_consolidate_key(vg_exec_context_t *vxcp)
{
	if (vxcp->vxc_delta) {
                // privkey += delta
		BN_clear(&vxcp->vxc_bntmp);
		BN_set_word(&vxcp->vxc_bntmp, vxcp->vxc_delta);
		BN_add(&vxcp->vxc_bntmp2,
		       EC_KEY_get0_private_key(vxcp->vxc_key),
		       &vxcp->vxc_bntmp);
		vg_set_privkey(&vxcp->vxc_bntmp2, vxcp->vxc_key);
                // delta = 0
		vxcp->vxc_delta = 0;
	}
}

void
vg_exec_context_calc_address(vg_exec_context_t *vxcp)
{
	EC_POINT *pubkey;
	const EC_GROUP *pgroup;
	unsigned char eckey_buf[96], hash1[32], hash2[20];
	int len;

	vg_exec_context_consolidate_key(vxcp);
	pgroup = EC_KEY_get0_group(vxcp->vxc_key);
	pubkey = EC_POINT_new(pgroup);
	EC_POINT_copy(pubkey, EC_KEY_get0_public_key(vxcp->vxc_key));
	if (vxcp->vxc_vc->vc_pubkey_base) {
		EC_POINT_add(pgroup,
			     pubkey,
			     pubkey,
			     vxcp->vxc_vc->vc_pubkey_base,
			     vxcp->vxc_bnctx);
	}
	len = EC_POINT_point2oct(pgroup,
				 pubkey,
				 vxcp->vc_combined_compressed ? POINT_CONVERSION_COMPRESSED : POINT_CONVERSION_UNCOMPRESSED,
				 eckey_buf,
				 sizeof(eckey_buf),
				 vxcp->vxc_bnctx);
	SHA256(eckey_buf, len, hash1);
	RIPEMD160(hash1, sizeof(hash1), hash2);
	memcpy(&vxcp->vxc_binres[1],
	       hash2, 20);
	EC_POINT_free(pubkey);
}

enum {
	timing_hist_size = 5
};

typedef struct _timing_info_s {
	struct _timing_info_s	*ti_next;
	pthread_t		ti_thread;
	unsigned long		ti_last_rate;

	unsigned long long	ti_hist_time[timing_hist_size];
	unsigned long		ti_hist_work[timing_hist_size];
	int			ti_hist_last;
} timing_info_t;

static pthread_mutex_t timing_mutex = PTHREAD_MUTEX_INITIALIZER;

int
vg_output_timing(vg_context_t *vcp, int cycle, struct timeval *last)
{
	pthread_t me;
	struct timeval tvnow, tv;
	timing_info_t *tip, *mytip;
	unsigned long long rate, myrate = 0, mytime, total, sincelast;
	int p, i;

	/* Compute the rate */
	gettimeofday(&tvnow, NULL);
	timersub(&tvnow, last, &tv);
	memcpy(last, &tvnow, sizeof(*last));
	mytime = tv.tv_usec + (1000000ULL * tv.tv_sec);
	if (!mytime)
		mytime = 1;
	rate = 0;

	pthread_mutex_lock(&timing_mutex);
	me = pthread_self();
	for (tip = vcp->vc_timing_head, mytip = NULL;
	     tip != NULL; tip = tip->ti_next) {
		if (pthread_equal(tip->ti_thread, me)) {
			mytip = tip;
			p = ((tip->ti_hist_last + 1) % timing_hist_size);
			tip->ti_hist_time[p] = mytime;
			tip->ti_hist_work[p] = cycle;
			tip->ti_hist_last = p;

			mytime = 0;
			myrate = 0;
			for (i = 0; i < timing_hist_size; i++) {
				mytime += tip->ti_hist_time[i];
				myrate += tip->ti_hist_work[i];
			}
			myrate = (myrate * 1000000) / mytime;
			tip->ti_last_rate = myrate;
			rate += myrate;

		} else
			rate += tip->ti_last_rate;
	}
	if (!mytip) {
		mytip = (timing_info_t *) malloc(sizeof(*tip));
		mytip->ti_next = vcp->vc_timing_head;
		mytip->ti_thread = me;
		vcp->vc_timing_head = mytip;
		mytip->ti_hist_last = 0;
		mytip->ti_hist_time[0] = mytime;
		mytip->ti_hist_work[0] = cycle;
		for (i = 1; i < timing_hist_size; i++) {
			mytip->ti_hist_time[i] = 1;
			mytip->ti_hist_work[i] = 0;
		}
		myrate = ((unsigned long long)cycle * 1000000) / mytime;
		mytip->ti_last_rate = myrate;
		rate += myrate;
	}

	vcp->vc_timing_total += cycle;
	if (vcp->vc_timing_prevfound != vcp->vc_found) {
		vcp->vc_timing_prevfound = vcp->vc_found;
		vcp->vc_timing_sincelast = 0;
	}
	vcp->vc_timing_sincelast += cycle;

	if (mytip != vcp->vc_timing_head) {
		pthread_mutex_unlock(&timing_mutex);
		return myrate;
	}
	total = vcp->vc_timing_total;
	sincelast = vcp->vc_timing_sincelast;
	pthread_mutex_unlock(&timing_mutex);

	vcp->vc_output_timing(vcp, sincelast, rate, total);
	return myrate;
}

void
vg_context_thread_exit(vg_context_t *vcp)
{
	timing_info_t *tip, **ptip;
	pthread_t me;

	pthread_mutex_lock(&timing_mutex);
	me = pthread_self();
	for (ptip = &vcp->vc_timing_head, tip = *ptip;
	     tip != NULL;
	     ptip = &tip->ti_next, tip = *ptip) {
		if (!pthread_equal(tip->ti_thread, me))
			continue;
		*ptip = tip->ti_next;
		free(tip);
		break;
	}
	pthread_mutex_unlock(&timing_mutex);

}

static void
vg_timing_info_free(vg_context_t *vcp)
{
	timing_info_t *tp;
	while (vcp->vc_timing_head != NULL) {
		tp = vcp->vc_timing_head;
		vcp->vc_timing_head = tp->ti_next;
		free(tp);
	}
}

void
vg_output_timing_console(vg_context_t *vcp, double count,
			 unsigned long long rate, unsigned long long total)
{
	double targ;
	char *unit;
	char linebuf[160];
	int rem, p;
    char *pkey_buf;
    double total_readable = total;
    char total_unit = ' ';
    vg_exec_context_t *vxcp = vcp->vc_threads;
printf("reached the line!\n");

	targ = rate;
	unit = "key/s";
	if (targ > 1000) {
		unit = "Kkey/s";
		targ /= 1000.0;
		if (targ > 1000) {
			unit = "Mkey/s";
			targ /= 1000.0;
		}
	}

	if (total_readable > 1000000) {
		total_unit = 'M';
		total_readable /= 1000000.0;
		if (total_readable > 1000) {
			total_unit = 'G';
			total_readable /= 1000.0;
		}
	}

	rem = sizeof(linebuf);
    pkey_buf = BN_bn2hex(EC_KEY_get0_private_key(vxcp->vxc_key));

	p = snprintf(linebuf, rem, "[%.2f %s][total %.2f %c][address %s][gpu ret %d]",
		     targ, unit, total_readable, total_unit, pkey_buf, vcp->vc_found_from_gpu);

    if (pkey_buf)
        OPENSSL_free(pkey_buf);

	assert(p > 0);
	rem -= p;
	if (rem < 0)
		rem = 0;

	if (rem) {
		memset(&linebuf[sizeof(linebuf)-rem], 0x20, rem);
		linebuf[sizeof(linebuf)-1] = '\0';
	}
	printf("\r%s", linebuf);
	fflush(stdout);

	/* write gpu fail addresses to file */
    if (vcp->vc_found_from_gpu == 1 && 0 != str_cmp((const unsigned char *) vcp->vc_found_from_gpu_addr, (const unsigned char *) vcp->vc_stored_gpu_addr, 64)) {
        char addr_buf[64];
        EC_KEY *pkey_temp = vxcp->vxc_key;
        BIGNUM *bn_temp;
        BIGNUM *save_pkey = BN_dup(EC_KEY_get0_private_key(vxcp->vxc_key));

        BN_hex2bn(&bn_temp, vcp->vc_found_from_gpu_addr);
        vg_set_privkey(bn_temp, pkey_temp);
        vg_encode_address((EC_POINT *) EC_KEY_get0_public_key(pkey_temp),
                          EC_KEY_get0_group(pkey_temp),
                          vcp->vc_pubkeytype, addr_buf);

        vg_set_privkey(save_pkey, vxcp->vxc_key);


        strncpy(vcp->vc_stored_gpu_addr, vcp->vc_found_from_gpu_addr, 66);
        FILE *fp = fopen("gpu_fails.txt", "a");
        if (!fp) {
            fprintf(stderr,
                    "ERROR: could not open result file: %s\n",
                    strerror(errno));
        } else {
            fprintf(fp,
                    "Address: %s\nPrivate: %s\n",
                    addr_buf, vcp->vc_found_from_gpu_addr);
            fclose(fp);
        }

        BN_free(save_pkey);
    }
}

void
//vg_output_match_console(vg_context_t *vcp, EC_KEY *pkey, const char *pattern)
vg_output_match_console(vg_context_t *vcp, vg_exec_context_t *vxcp, const char *pattern)
{
	unsigned char key_buf[512], *pend;
	char addr_buf[64], addr2_buf[64];
	char privkey_buf[128];
	char * privkey_str = privkey_buf;
	const char *keytype = "Privkey";
	int len;
	int isscript = (vcp->vc_format == VCF_SCRIPT);
	EC_KEY *pkey = vxcp->vxc_key;
	EC_POINT *ppnt;
	int free_ppnt = 0;
	if (vcp->vc_pubkey_base) {
		ppnt = EC_POINT_new(EC_KEY_get0_group(pkey));
		EC_POINT_copy(ppnt, EC_KEY_get0_public_key(pkey));
		EC_POINT_add(EC_KEY_get0_group(pkey),
			     ppnt,
			     ppnt,
			     vcp->vc_pubkey_base,
			     NULL);
		free_ppnt = 1;
		keytype = "PrivkeyPart";
	} else {
		ppnt = (EC_POINT *) EC_KEY_get0_public_key(pkey);
	}

	assert(EC_KEY_check_key(pkey));
//	if (vcp->vc_combined_compressed)
	if (vxcp->vc_combined_compressed)
		vg_encode_address_compressed(ppnt,
				  EC_KEY_get0_group(pkey),
				  vcp->vc_pubkeytype, addr_buf);
	else
		vg_encode_address(ppnt,
				  EC_KEY_get0_group(pkey),
				  vcp->vc_pubkeytype, addr_buf);
	if (isscript)
		vg_encode_script_address(ppnt,
					 EC_KEY_get0_group(pkey),
					 vcp->vc_addrtype, addr2_buf);

	if (vcp->vc_key_protect_pass) {
		len = vg_protect_encode_privkey(privkey_buf,
						pkey, vcp->vc_privtype,
						VG_PROTKEY_DEFAULT,
						vcp->vc_key_protect_pass);
		if (len) {
			keytype = "Protkey";
		} else {
			fprintf(stderr,
				"ERROR: could not password-protect key\n");
			vcp->vc_key_protect_pass = NULL;
		}
	}
	if (!vcp->vc_key_protect_pass) {
//		if (vcp->vc_combined_compressed)
		privkey_str = BN_bn2hex(EC_KEY_get0_private_key(pkey));
		//printf("Privkey (hex): %s\n", privkey_str);
	/*
		if (vxcp->vc_combined_compressed)
			vg_encode_privkey_compressed(pkey, vcp->vc_privtype, privkey_buf);
		else
			vg_encode_privkey(pkey, vcp->vc_privtype, privkey_buf);
		*/
	}

	if (!vcp->vc_result_file || (vcp->vc_verbose > 1)) {
		//printf("\r%79s\rPattern: %s\n", "", pattern);
	}

	if (vcp->vc_verbose > 0) {
		if (vcp->vc_verbose > 1) {
			pend = key_buf;
			len = i2o_ECPublicKey(pkey, &pend);
			printf("Pubkey (hex): ");
			dumphex(key_buf, len);
			pend = key_buf;
			len = i2d_ECPrivateKey(pkey, &pend);
			printf("Privkey (ASN1): ");
			dumphex(key_buf, len);
		}

	}

	if (!vcp->vc_result_file || (vcp->vc_verbose > 0)) {
		if (isscript)
			printf("P2SHAddress: %s\n", addr2_buf);
		printf("\nAddress: %s\n"
		       "%s (hex): %s\n",
		       addr_buf, keytype, privkey_str);
	}

	if (vcp->vc_result_file) {
		FILE *fp = fopen(vcp->vc_result_file, "a");
		if (!fp) {
			fprintf(stderr,
				"ERROR: could not open result file: %s\n",
				strerror(errno));
		} else {
			if (isscript)
				fprintf(fp, "P2SHAddress: %s\n", addr2_buf);
			fprintf(fp,
				"Address: %s\n"
				"%s (hex): %s\n",
				addr_buf, keytype, privkey_str);
			fclose(fp);
		}
	}
	if (free_ppnt)
		EC_POINT_free(ppnt);
}


void
vg_context_free(vg_context_t *vcp)
{
	vg_timing_info_free(vcp);
	vcp->vc_free(vcp);
}

int
vg_context_add_patterns(vg_context_t *vcp,
			const char ** const patterns, int npatterns)
{
	printf("Searching for %d addresses\n", npatterns);
	vcp->patterns = (char*)calloc(20 /* address size */, npatterns);
	char ** prefix_ = (char ** ) malloc(sizeof(char *) * npatterns);
        for (int i=0; i<npatterns; i++) {
            int len = strlen(patterns[i]);
            while (len) if (strchr(" \r\n\t", patterns[i][len-1])) len--; else break;
            if (len != 33 && len != 34) {
                    printf("Wrong address length at line %d: %d (must be 33 or 34)\n", i+1, len);
                    exit(-1);
            }

            char buf[21];
            if (!vg_b58_decode_check(patterns[i], buf, 21)) return 0;
            memcpy(vcp->patterns+i*20, buf+1, 20);

            prefix_[i] = (char *) malloc(sizeof(char) * 21);
            memcpy(prefix_[i], buf + 1, 20);
            prefix_[i][20] = 0;
        }

	return vcp->vc_add_patterns(vcp, (const char ** const) prefix_, npatterns);
}

void
vg_context_clear_all_patterns(vg_context_t *vcp)
{
        free(vcp->patterns);
        vcp->patterns = NULL;
}

int
vg_context_start_threads(vg_context_t *vcp)
{
	vg_exec_context_t *vxcp;
	int res;

	for (vxcp = vcp->vc_threads; vxcp != NULL; vxcp = vxcp->vxc_next) {
        if (vcp->vc_verbose > 1) printf("\nStart a thread");
		res = pthread_create((pthread_t *) &vxcp->vxc_pthread,
				     NULL,
				     (void *(*)(void *)) vxcp->vxc_threadfunc,
				     vxcp);
		if (res) {
			fprintf(stderr, "ERROR: could not create thread: %d\n",
				res);
			vg_context_stop_threads(vcp);
			return -1;
		}
		vxcp->vxc_thread_active = 1;
	}
	return 0;
}

void
vg_context_stop_threads(vg_context_t *vcp)
{
	vcp->vc_halt = 1;
	vg_context_wait_for_completion(vcp);
	vcp->vc_halt = 0;
}

void
vg_context_wait_for_completion(vg_context_t *vcp)
{
	vg_exec_context_t *vxcp;

	for (vxcp = vcp->vc_threads; vxcp != NULL; vxcp = vxcp->vxc_next) {
		if (!vxcp->vxc_thread_active)
			continue;
		pthread_join((pthread_t) vxcp->vxc_pthread, NULL);
		vxcp->vxc_thread_active = 0;
	}
}

//#defined DEBUG_PREFIXES

static vg_pattern_t *
vg_pattern_search(vg_pattern_root_t *rootp, unsigned char * pattern)
{
	vg_pattern_t *itemp = rootp->next;

	while (itemp) {
		int cmp = str_cmp(pattern, itemp->prefix, 20);
		if (cmp > 0) itemp = itemp->next;
		else if (cmp == 0) return itemp;
		else break;
	}

	return NULL;
}

static void
vg_prefix_add(vg_pattern_root_t *rootp, const unsigned char *pattern)
{
#ifdef DEBUG_PREFIXES
	printf("vg_prefix_add >> ");
	dumphex(pattern, 20);
#endif
	vg_pattern_t *item = (vg_pattern_t *)malloc(sizeof(vg_pattern_t));
	item->prefix = pattern;
	item->next = NULL;
	item->prev = NULL;

	if (!rootp->next) {
		rootp->next = item;
#ifdef DEBUG_PREFIXES
		printf("vg_prefix_add >> add root elem\n");
#endif
	}
	else {
		vg_pattern_t *tmp_this = rootp->next, *tmp_prev = NULL;
		while (tmp_this) {
			int _res = str_cmp(pattern, tmp_this->prefix, 20);
			if (_res > 0) {
#ifdef DEBUG_PREFIXES
                printf("vg_prefix_add >> prefix is higher, go for the next\n");
#endif
				tmp_prev = tmp_this;
				tmp_this = tmp_this->next;
				continue;
			}
			else if (_res == 0) {
				//equals so ignore this prefix
				printf("This pattern is already in the list\n");
				dumphex(pattern, 20);
				return;
			}

			if (!tmp_this->prev) {
#ifdef DEBUG_PREFIXES
				printf("vg_prefix_add >> add to the head\n");
#endif
				rootp->next = item;
			}
			else {
#ifdef DEBUG_PREFIXES
				printf("vg_prefix_add >> insert\n");
#endif
				item->prev = tmp_this->prev;
				item->prev->next = item;
			}
            item->next = tmp_this;
            item->next->prev = item;
			break;
		}

		if (!tmp_this) {
#ifdef DEBUG_PREFIXES
			printf("vg_prefix_add >> add to the tail\n");
#endif
			item->prev = tmp_prev;
			tmp_prev->next = item;
		}
	}
}

static void
vg_prefix_context_clear_all_patterns(vg_context_t *vcp)
{
	vg_pattern_t *item = vcp->vc_pattern_root->next;
	while (item) {
		vg_pattern_t *tmp_next = item->next;
		free(item);
		item=tmp_next;
	}

	vcp->vc_npatterns = 0;
	vcp->vc_npatterns_start = 0;
	vcp->vc_found = 0;
}

static void
vg_prefix_context_free(vg_context_t *vcp)
{
	vg_prefix_context_clear_all_patterns(vcp);
	free(vcp->vc_pattern_root);
}

#define PRINT_PREFIXES
static int
vg_prefix_context_add_patterns(vg_context_t *vcp,
			       const char ** const patterns, int npatterns)
{
	BN_CTX *bnctx;
	BIGNUM bntmp, bntmp2, bntmp3;
	int i;
	vg_pattern_t *itemp;

	bnctx = BN_CTX_new();
	BN_init(&bntmp);
	BN_init(&bntmp2);
	BN_init(&bntmp3);

	for (i = 0; i < npatterns; i++) {
		vg_prefix_add(vcp->vc_pattern_root, (const unsigned char *)patterns[i]);
	}

	itemp = vcp->vc_pattern_root->next;
#ifdef PRINT_PREFIXES
	while(itemp) {
		printf("Pattern ");
		dumphex(itemp->prefix, 20);
		itemp = itemp->next;
	}
#endif

	vcp->vc_npatterns = npatterns;

	BN_clear_free(&bntmp);
	BN_clear_free(&bntmp2);
	BN_clear_free(&bntmp3);
	BN_CTX_free(bnctx);
	return 1;
}

static int
vg_prefix_test(vg_exec_context_t *vxcp)
{
	vg_context_t *vcp = vxcp->vxc_vc;
	vg_pattern_t *vp;
	int res = 0;

	/*
	 * We constrain the prefix so that we can check for
	 * a match without generating the lower four byte
	 * check code.
	 */

	BN_bin2bn(vxcp->vxc_binres, 25, &vxcp->vxc_bntarg);
	//char addr[35];
	//vg_b58_encode_check(vxcp->vxc_binres, 21, addr);

research:
	vp = vg_pattern_search(vcp->vc_pattern_root, vxcp->vxc_binres+1);
	if (vp) {
		if (vg_exec_context_upgrade_lock(vxcp))
			goto research;

		vg_exec_context_consolidate_key(vxcp);
		vcp->vc_output_match(vcp, vxcp,
							 (const char *)vp->prefix);

		vcp->vc_found++;

		if (vcp->vc_only_one) {
			return 2;
		}

		res = 1;
	}
	return res;
}

vg_context_t *
vg_prefix_context_new(int addrtype, int privtype, int caseinsensitive)
{
	vg_context_t *vcp = NULL;

	vcp = (vg_context_t *) malloc(sizeof(*vcp));
	if (vcp) {
		memset(vcp, 0, sizeof(*vcp));
		vcp->vc_addrtype = addrtype;
		vcp->vc_privtype = privtype;
		vcp->vc_npatterns = 0;
		vcp->vc_npatterns_start = 0;
		vcp->vc_found = 0;
		vcp->vc_chance = 0.0;
		vcp->vc_free = vg_prefix_context_free;
		vcp->vc_add_patterns = vg_prefix_context_add_patterns;
		vcp->vc_clear_all_patterns =
			vg_prefix_context_clear_all_patterns;
		vcp->vc_test = vg_prefix_test;
		vcp->vc_hash160_sort = NULL;

		vcp->vc_pattern_root = (vg_pattern_root_t *)malloc(sizeof(vg_pattern_root_t));
		vcp->vc_pattern_root->next = NULL;
	}
	return vcp;
}
