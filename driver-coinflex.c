
/*
 * Copyright 2012-2013 Andrew Smith
 * Copyright 2012 Luke Dashjr
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by the Free
 * Software Foundation; either version 3 of the License, or (at your option)
 * any later version.  See COPYING for more details.
 */

//=====================================================================//
//***   driver-coinflex.c is for X11 algorithm mining by using Han-Lab's Pantheon-XXX series miner      ***//
//=====================================================================//

//=====================================================================//
//  DRIVER_COINFLEX DEFINITION FOR X11 ALGORITHM
//  Support Product:
//      1) Pantheon-A   : Altera Stratix V E9 FPGA Chip
//                      : 1 base b'd, 10 miner b'd, 1 miner b'd includes 4EA FPGA Chip
//      2) Pantheon-AFS4    : Altera Stratix IV 530 FPGA Chip
//                      : 2 miner b'd(operating independently), 1 miner b'd includes 10EA FPGA Chip
//      3) Pantheon-CMF1 : Altera Stratix V E9 FPGA Chip
//                      :  1 base b'd, 1 core b'd, 1 core b'd includes 1EA FPGA Chip
//=====================================================================//


#include "config.h"

#include <stdarg.h>
#include <stdio.h>
#include <unistd.h>
#include <math.h>
#include <pthread.h>
#include <error.h>

#include "logging.h"
#include "miner.h"
//#include "usbutils.h"
#include "util.h"
#include "driver-coinflex.h"
#include "compat.h"


#include "spi-context.h"
#include "logging.h"
#include "miner.h"
#include "util.h"

#include "A1-board-selector.h"
#include "A1-trimpot-mcp4x.h"

#include "asic_b52.h"
#include "mcompat_chain.h"
#include "mcompat_tempctrl.h"
#include "mcompat_fanctrl.h"

int chain_encore_flag[ASIC_CHAIN_NUM] = {0};

#define WORK_SIZE               (80)
#define DEVICE_TARGET_SIZE      (32)
#define TARGET_POS              (80)
#define TARGET_SIZE             (4)
#define MINER_ID_POS            (84)
#define MINER_ID_SIZE           (1)
#define WORK_ID_POS             (85)
#define WORK_ID_SIZE            (1)
#define FIND_NONCE_SIZE         (6)             // For receive value from miner: 4-Bytes nonce, 1-Byte miner_id, 1-Byte work_id

#define REPLY_SIZE              (2)
#define BUF_SIZE                (128)
//#define TEMP_UPDATE_INT_MS  10000
#define CHECK_DISABLE_TIME  0

#define DIFF_DEF		(128)
#define DIFF_1HR		(256)
#define DIFF_4HR		(512)
#define DIFF_RUN		(1024)

static int ret_pll[ASIC_CHAIN_NUM] = {0};

struct A1_chain *chain[ASIC_CHAIN_NUM];

static uint32_t show_log[ASIC_CHAIN_NUM];
static uint32_t update_temp[ASIC_CHAIN_NUM];
static uint32_t check_disbale_flag[ASIC_CHAIN_NUM];
static volatile uint8_t g_debug_stats[ASIC_CHAIN_NUM];

int spi_plug_status[ASIC_CHAIN_NUM] = {0};

char szShowLog[ASIC_CHAIN_NUM][ASIC_CHIP_NUM][256] = {0};
char volShowLog[ASIC_CHAIN_NUM][256] = {0};

hardware_version_e g_hwver;
b52_type_e g_type;
int g_reset_delay = 0xffff;
int g_miner_state = 0;
int chain_flag[ASIC_CHAIN_NUM] = {0};

/* added by yex in 20170907 */
/*
 * if not cooled sufficiently, communication fails and chip is temporary
 * disabled. we let it inactive for 30 seconds to cool down
 *
 * TODO: to be removed after bring up / test phase
 */

/*
 * for now, we have one global config, defaulting values:
 * - ref_clk 16MHz / sys_clk 800MHz
 * - 2000 kHz SPI clock
 */
struct A1_config_options A1_config_options = {
    .ref_clk_khz = 16000, .sys_clk_khz = 800000, .spi_clk_khz = 2000,
};

/* override values with --bitmine-a1-options ref:sys:spi: - use 0 for default */
static struct A1_config_options *parsed_config_options;


#if COINFLEX_TEST_MODE
static void coinflex_set_testdata(struct work *work);
static void coinflex_print_hash(struct work *work, uint32_t nonce);
#endif

static void get_temperatures(struct A1_chain *a1)
{
	int i;
	int temp[MAX_CHIP_NUM] = {0};
	c_temp temp_stat;

	/* Get temperature for each chip */
	mcompat_get_chip_temp(a1->chain_id, temp);
	for (i = 0; i < a1->num_active_chips; i++)
		a1->chips[i].temp = temp[i];

	/* Get temperature stat. */
	mcompat_stat_chain_temp(temp, &temp_stat);
	a1->temp     = temp_stat.tmp_avg;
	a1->temp_max = temp_stat.tmp_hi;
	a1->temp_min = temp_stat.tmp_lo;
}

static void get_voltages(struct A1_chain *a1)
{
	int i;
	int volt[MAX_CHIP_NUM] = {0};
	c_volt volt_stat;

	/* configure for vsensor */
	mcompat_configure_tvsensor(a1->chain_id, CMD_ADDR_BROADCAST, 0);

	/* Get voltage for each chip */
	mcompat_get_chip_volt(a1->chain_id, volt);
	for (i = 0; i < a1->num_active_chips; i++)
    {
        applog(LOG_NOTICE,"chain:%d,chip:%d,vol:%d",a1->chain_id,i+1,volt[i]);
		a1->chips[i].nVol = volt[i];
       }
	/* Get voltage stat. */
	mcompat_stat_chain_volt(volt, &volt_stat);
	a1->volt	 = volt_stat.vol_avg;
	a1->volt_max = volt_stat.vol_hi;
	a1->volt_min = volt_stat.vol_lo;

	/* configure for tsensor */
	mcompat_configure_tvsensor(a1->chain_id, CMD_ADDR_BROADCAST, 1);
}

//static void coinflex_print_hw_error(char *drv_name, int device_id, struct work *work, uint32_t nonce);
//static bool coinflex_set_algorithm(struct cgpu_info *coinflex);

/********** work queue */
static bool wq_enqueue(struct work_queue *wq, struct work *work)
{
    if (work == NULL)
        return false;

    struct work_ent *we = malloc(sizeof(*we));
    assert(we != NULL);

    we->work = work;
    INIT_LIST_HEAD(&we->head);
    list_add_tail(&we->head, &wq->head);
    wq->num_elems++;
    return true;
}

static struct work *wq_dequeue(struct work_queue *wq)
{
    if (wq == NULL)
        return NULL;
    if (wq->num_elems == 0)
        return NULL;
    struct work_ent *we;
    we = list_entry(wq->head.next, struct work_ent, head);
    struct work *work = we->work;

    list_del(&we->head);
    free(we);
    wq->num_elems--;
    return work;
}

/* queue two work items per chip in chain */
static bool coinflex_queue_full(struct cgpu_info *cgpu)
{
    struct A1_chain *a1 = cgpu->device_data;
    int queue_full = false;

    mutex_lock(&a1->lock);
    //  applog(LOG_NOTICE, "%d, A1 running queue_full: %d/%d",
    //     a1->chain_id, a1->active_wq.num_elems, a1->num_active_chips);

    if (a1->active_wq.num_elems >= a1->num_active_chips * 2)
        queue_full = true;
    else
        wq_enqueue(&a1->active_wq, get_queued(cgpu));

    mutex_unlock(&a1->lock);

    return queue_full;
}

void exit_A1_chain(struct A1_chain *a1)
{
    if (a1 == NULL){
        return;
    }
    free(a1->chips);

    mcompat_chain_power_down(a1->chain_id);

    a1->chips = NULL;
    free(a1);
}

static void performance_cfg(void)
{
	int i, vid;
	
	if (opt_A1auto) {
		/* different pll depending on performance strategy. */
		if (opt_A1_factory){
			opt_A1Pll1 = CHIP_PLL_FAC;
			vid = CHIP_VID_FAC;
		}	
		else if (opt_A1_performance){
			opt_A1Pll1 = CHIP_PLL_PER;
			vid = CHIP_VID_PER;
		}	
		else if (opt_A1_efficient){
			opt_A1Pll1 = CHIP_PLL_EFF;
			vid = CHIP_VID_EFF;
		}
		else{			
			opt_A1Pll1 = CHIP_PLL_BAL;
			vid = CHIP_VID_BAL;
		}	

		for (i = 0; i < MAX_CHAIN_NUM; ++i)
			opt_voltage[i] = vid;
	}
}

void miner_get_encore_flag(int chain_id)
{
	FILE* fd;
	int retryCnt;
	char fileName[128];

	sprintf(fileName, "%s%d.log", LOG_FILE_ENCORE_PREFIX, chain_id);
	if ((access(fileName, F_OK)) != -1) {
		applog(LOG_ERR, "Miner init encore retry file already exists!");
		fd = fopen(fileName, "r+");
		if (fd == NULL) {
			applog(LOG_ERR, "Open miner init encore retry file failed!");
			return;
		}
		if (fscanf(fd, "%d", &retryCnt) < 1)
			applog(LOG_ERR, "Fscanf of miner init encore retry file failed!");
		else {
			applog(LOG_INFO, "Miner init encore retry count is %d!", retryCnt);
			chain_encore_flag[chain_id] = retryCnt;
		}
		fclose(fd);
	}
	return;
}

void miner_encore_save(void)
{
	FILE* fd;
	int i;

	for (i = 0; i < ASIC_CHAIN_NUM; i++) {
		char fileName[128];

		if (chain_flag[i] != 1 || !chain_encore_flag[i])
			continue;

		sprintf(fileName, "%s%d.log", LOG_FILE_ENCORE_PREFIX, i);
		fd = fopen(fileName, "w+");
		if (fd == NULL){
			applog(LOG_ERR, "Open to write miner encore retry file failed!");
			return;
		}
		fprintf(fd, "%d", chain_encore_flag[i]);
		fclose(fd);
	}
}

static bool check_chips(struct A1_chain *a1)
{
	int i;
	int cores[MAX_CHIP_NUM] = {0};
	char errmsg[64];

	if (mcompat_chain_get_chip_cores(a1->chain_id, a1->num_active_chips, cores)) {
		a1->num_cores = 0;
		for (i = 0; i < a1->num_active_chips; i++) {
			if (cores[i] > ASIC_CORE_NUM) {
				applog(LOG_WARNING, "chain%d: chip%d invalid core number(%d), set to default(%d)",
					a1->chain_id, i + 1, cores[i], ASIC_CORE_NUM);
				cores[i] = ASIC_CORE_NUM;
			} else if (cores[i] < ASIC_CORE_NUM) {
				applog(LOG_WARNING, "chain%d: chip%d core number(%d) < %d",
					a1->chain_id, i + 1, cores[i], ASIC_CORE_NUM);
			}

			a1->chips[i].num_cores = cores[i];
			a1->num_cores += cores[i];

			if (a1->chips[i].num_cores < BROKEN_CHIP_THRESHOLD) {
				applog(LOG_WARNING, "%d: broken chip %d with %d active cores (threshold = %d)",
					a1->chain_id, i + 1, a1->chips[i].num_cores, BROKEN_CHIP_THRESHOLD);
				a1->chips[i].disabled = true;
				a1->num_cores -= a1->chips[i].num_cores;

				sprintf(errmsg, "%d:%d", a1->chain_id, i + 1);
				if (mcompat_set_errcode(ERRCODE_INV_CORENUM, errmsg, false))
					mcompat_save_errcode();

				goto failure;
			}

			if (a1->chips[i].num_cores < WEAK_CHIP_THRESHOLD) {
				applog(LOG_WARNING, "%d: weak chip %d with %d active cores (threshold = %d)",
					a1->chain_id, i + 1, a1->chips[i].num_cores, WEAK_CHIP_THRESHOLD);

				sprintf(errmsg, "%d:%d", a1->chain_id, i + 1);
				if (mcompat_set_errcode(ERRCODE_INV_CORENUM, errmsg, false))
					mcompat_save_errcode();

				goto failure;
			}

			/* Reenable this in case we have cycled through this function more than
			 * once. */
			a1->chips[i].disabled = false;
		}

		return true;
	} else {
		sprintf(errmsg, "%d", a1->chain_id);
		if (mcompat_set_errcode(ERRCODE_INV_CORENUM, errmsg, false))
			mcompat_save_errcode();
		goto failure;
	}

failure:
	g_chain_alive[a1->chain_id] = 0;
	mcompat_chain_power_down(a1->chain_id);
	return false;
}

static bool chain_restart(struct A1_chain *a1, int retry_cnt, int retry_intval)
{
	int retries = 0;
	c_chain_param chain_param;

	applog(LOG_NOTICE, "chain%d: restarting", a1->chain_id);

	chain_param.chain_id = a1->chain_id;
	chain_param.spi_speed = SPI_SPEED_RUN;
	chain_param.pll = opt_A1Pll1;
	chain_param.vol = 0;
	chain_param.vid = opt_voltage[a1->chain_id];
	chain_param.tuning = false;
	applog(LOG_NOTICE, "\tparam->pll: %d", chain_param.pll);
	applog(LOG_NOTICE, "\tparam->vol: %d", chain_param.vol);
	applog(LOG_NOTICE, "\tparam->vid: %d", chain_param.vid);

	while(retries < retry_cnt) {
		mcompat_chain_detect_thread((void*)&chain_param);
		if (g_chain_alive[a1->chain_id] && check_chips(a1)) {
			applog(LOG_NOTICE, "chain%d: detected %d chips / %d cores",
				a1->chain_id, a1->num_active_chips, a1->num_cores);

			get_voltages(a1);

			struct timeval now;
			cgtime(&now);
			a1->lastshare = now.tv_sec;

			break;
		}

		applog(LOG_ERR, "chain%d: failed to restart, retry(%d) after %d seconds",
			a1->chain_id, ++retries, retry_intval);
		sleep(retry_intval);
	}

	return g_chain_alive[a1->chain_id];
}


static bool chain_detect_all()
{
	int i, j, cid;
	c_chain_param chain_params[MAX_CHAIN_NUM];

	applog(LOG_DEBUG, "D9 detect");

	/* Init temp ctrl */
	c_temp_cfg tmp_cfg;
	mcompat_tempctrl_get_defcfg(&tmp_cfg);
	/* Set initial target temperature lower for more reliable startup */
	tmp_cfg.tmp_target	 = 75;
	tmp_cfg.tmp_thr_pd	 = 105;
	tmp_cfg.tmp_thr_warn = 110;		/* avoid throttle during startup */
	tmp_cfg.tmp_exp_time = 2000;
	mcompat_tempctrl_init(&tmp_cfg);

	/* Init fan ctrl thread */
	c_fan_cfg fan_cfg;
	mcompat_fanctrl_get_defcfg(&fan_cfg);
	fan_cfg.preheat = false;		/* disable preheat */
	fan_cfg.fan_mode = g_auto_fan ? FAN_MODE_AUTO : FAN_MODE_MANUAL;
	fan_cfg.fan_speed_manual = g_fan_speed;
	fan_cfg.fan_speed_target = 80;
	mcompat_fanctrl_init(&fan_cfg);
//	mcompat_fanctrl_init(NULL); 	// using default cfg
	pthread_t tid;
	pthread_create(&tid, NULL, mcompat_fanctrl_thread, NULL);

	/* Register PLL map config */
	mcompat_chain_set_pllcfg(g_pll_list, g_pll_regs, PLL_LV_NUM);

	/* Determine working PLL & VID */
	performance_cfg();

	for (i = 0; i < g_chain_num; ++i) {
		cid = g_chain_id[i];
		chain_params[i].chain_id = cid;
		chain_params[i].spi_speed = SPI_SPEED_RUN;
		chain_params[i].pll = opt_A1Pll1;
		chain_params[i].vol = 0;		/* Set to 0 to disable voltage calibration */
		chain_params[i].vid = opt_voltage[cid];
		chain_params[i].tuning = false;
	}

	/* Detect all chains sequentially with fan bypass disabled during startup */
	if (0 == mcompat_chain_detect_all(0xff, chain_params, false, false))
		return false;
	
	mcompat_get_miner_status();
	
	for (i = 0; i < g_chain_num; ++i) {
		cid = g_chain_id[i];

		if (!g_chain_alive[cid])
			continue;

		/* Init chain object */
		chain[i] = malloc(sizeof(struct A1_chain));
		assert(chain[i] != NULL);
		memset(chain[i], 0, sizeof(struct A1_chain));

		chain[i]->chain_id = cid;
		chain[i]->pll = chain[i]->base_pll = mcompat_chain_pll_to_level(chain_params[i].pll);
		chain[i]->vid = chain_params[i].vid;
		chain[i]->num_active_chips = chain[i]->num_chips = chain_params[i].chip_num;

		/* Init chips */
		chain[i]->chips = calloc(chain[i]->num_active_chips, sizeof(struct A1_chip));
		assert (chain[i]->chips != NULL);

		/* Get core number for each chip */
		if (!check_chips(chain[i])) {
			free(chain[i]->chips);
			free(chain[i]);
			chain[i] = NULL;
			continue;
		}

		/* Init chip voltages */
		get_voltages(chain[i]);

		applog(LOG_NOTICE, "chain%d: detected %d chips / %d cores",
			cid, chain[i]->num_active_chips, chain[i]->num_cores);

		/* Init cgpu object */
		struct cgpu_info *cgpu = malloc(sizeof(*cgpu));
		assert(cgpu != NULL);
		memset(cgpu, 0, sizeof(*cgpu));
		cgpu->drv = &coinflex_drv;
		cgpu->name = "S11.SingleChain";
		cgpu->threads = 1;
		cgpu->chainNum = cid;
		cgpu->device_data = chain[i];
		if ((chain[i]->num_chips <= MAX_CHIP_NUM) && (chain[i]->num_cores <= MAX_CORES))
			cgpu->mhs_av = (double)opt_A1Pll1 * 2ull * (chain[i]->num_cores);
		else
			cgpu->mhs_av = 0;
		cgtime(&cgpu->dev_start_tv);
		chain[i]->lastshare = cgpu->dev_start_tv.tv_sec;
		chain[i]->cgpu = cgpu;
		add_cgpu(cgpu);

		/* Other init */
		mutex_init(&chain[i]->lock);
		INIT_LIST_HEAD(&chain[i]->active_wq.head);
	}

	/* Now adjust temperature config for runtime setting */
	g_tmp_cfg.tmp_thr_warn = 105;
	g_tmp_cfg.tmp_thr_pd = 110;

	return true;
}

static void coinflex_detect(bool __maybe_unused hotplug)
{
    if (hotplug){
        return;
    }

    struct timeval test_tv;
    int j = 0,i;

    /* parse bimine-a1-options */
    if ((opt_bitmine_a1_options != NULL) && (parsed_config_options == NULL)) {
        int ref_clk = 0;
        int sys_clk = 0;
        int spi_clk = 0;
        int override_chip_num = 0;
        int wiper = 0;

        sscanf(opt_bitmine_a1_options, "%d:%d:%d:%d:%d",&ref_clk, &sys_clk, &spi_clk, &override_chip_num,&wiper);
        if (ref_clk != 0){
            A1_config_options.ref_clk_khz = ref_clk;
        }
        if (sys_clk != 0) {
            if (sys_clk < 100000){
                quit(1, "system clock must be above 100MHz");
            }
            A1_config_options.sys_clk_khz = sys_clk;
        }
        if (spi_clk != 0){
            A1_config_options.spi_clk_khz = spi_clk;
        }
        if (override_chip_num != 0){
            A1_config_options.override_chip_num = override_chip_num;
        }
        if (wiper != 0){
            A1_config_options.wiper = wiper;
        }

        /* config options are global, scan them once */
        parsed_config_options = &A1_config_options;
    }

#if 0
    // update time
    for(j = 0; j < 64; j++)
    {
        cgtime(&test_tv);
        if(test_tv.tv_sec > 1000000000)
        {
            break;
        }

        usleep(500000);
    }
#endif

	/* Chain detect */
	if (chain_detect_all()) {
		applog(LOG_NOTICE, "S11 detect finish");
		return;
	}

	applog(LOG_ERR, "S11 detect failed");

}

static void coinflex_get_statline_before(char *buf, size_t bufsiz, struct cgpu_info *coinflex)
{
    struct A1_chain *a1 = coinflex->device_data;
    char temp[10];
    if (a1->temp != 0)
        snprintf(temp, 9, "%2dC", a1->temp);
    tailsprintf(buf, bufsiz, " %2d:%2d/%3d %s",
            a1->chain_id, a1->num_active_chips, a1->num_cores,
            a1->temp == 0 ? "   " : temp);
}

static void coinflex_flush_work(struct cgpu_info *coinflex)
{
    struct A1_chain *a1 = coinflex->device_data;
    int cid = a1->chain_id;
    //board_selector->select(cid);
    int i;
    uint8_t buffer[4] = {0};

    mutex_lock(&a1->lock);
    /* stop chips hashing current work */
  //  if (!abort_work(a1)) 
   // {
  //      applog(LOG_ERR, "%d: failed to abort work in chip chain!", cid);
  //  }
    /* flush the work chips were currently hashing */
    for (i = 0; i < a1->num_active_chips; i++) 
    {
        int j;
        struct A1_chip *chip = &a1->chips[i];
        for (j = 0; j < 4; j++) 
        {
            struct work *work = chip->work[j];
            if (work == NULL)
                continue;
//          applog(LOG_DEBUG, "%d: flushing chip %d, work %d: 0x%p",
//              cid, i, j + 1, work);
            work_completed(coinflex, work);
            chip->work[j] = NULL;
        }

        chip->last_queued_id = 0;

       // if(!mcompat_cmd_resetjob(a1->chain_id, i+1, buffer))
       // {
      //      applog(LOG_WARNING, "chip %d clear work failed", i);
      //      continue;
      //  }

        //applog(LOG_INFO, "chip :%d flushing queued work success", i);
    }
    /* flush queued work */
    //applog(LOG_DEBUG, "%d: flushing queued work...", cid);
    while (a1->active_wq.num_elems > 0) 
    {
        struct work *work = wq_dequeue(&a1->active_wq);
        assert(work != NULL);
        work_completed(coinflex, work);
    }
    mutex_unlock(&a1->lock);

}


#define VOLTAGE_UPDATE_INT  6000
//#define  LOG_FILE_PREFIX "/home/www/conf/analys"
#define  LOG_FILE_PREFIX "/tmp/log/analys"
#define  LOG_VOL_PREFIX "/tmp/log/volAnalys"


const char cLevelError1[3] = "!";
const char cLevelError2[3] = "#";
const char cLevelError3[3] = "$";
const char cLevelError4[3] = "%";
const char cLevelError5[3] = "*";
const char cLevelNormal[3] = "+";

void B52_Log_Save(struct A1_chip *chip,int nChip,int nChain)
{
    char szInNormal[8] = {0};
    memset(szInNormal,0, sizeof(szInNormal));
    if(chip->hw_errors > 0){
        strcat(szInNormal,cLevelError1);
    }
    if(chip->stales > 0){
        strcat(szInNormal,cLevelError2);
    }
    if((chip->temp > 564) || (chip->temp < 445)){
        strcat(szInNormal,cLevelError3);
    }
    if(chip->num_cores < 8){
        strcat(szInNormal,cLevelError4);
    }
    if((chip->nVol > 550) || (chip->nVol < 450)){
        strcat(szInNormal,cLevelError5);
    }

    if((chip->hw_errors == 0) && (chip->stales == 0) && ((chip->temp < 564) && (chip->temp > 445)) &&((chip->nVol < 550) && (chip->nVol > 450)) && (chip->num_cores == 8)){
        strcat(szInNormal,cLevelNormal);
    }

    sprintf(szShowLog[nChain][nChip], "\n%-8s|%32d|%8d|%8d|%8d|%8d|%8d|%8d|%8d",szInNormal,chip->nonces_found,
            chip->hw_errors, chip->stales,chip->temp,chip->nVol,chip->num_cores,nChip,nChain);
}

void b52_log_print(int cid, void* log, int len)
{
    FILE* fd;
    char fileName[128] = {0};

    sprintf(fileName, "%s%d.log", LOG_FILE_PREFIX, cid);
    
    fd = fopen(fileName, "w+"); 
    
    if(fd == NULL){             
        //applog(LOG_ERR, "Open log File%d Failed!%d", cid, errno);
        applog(LOG_ERR, "Open log File%d Failed!%s", cid, strerror(errno));
        return; 
    }

    fwrite(log, len, 1, fd);
    fflush(fd);
    fclose(fd);
}

void b52_log_record(int cid, void* log, int len)
{
    FILE* fd;
    char fileName[128] = {0};

    sprintf(fileName, "%s%d.log", LOG_VOL_PREFIX, cid);
    fd = fopen(fileName, "w+"); 
    if(fd == NULL){             
        //applog(LOG_ERR, "Open log File%d Failed!%d", cid, errno);
        applog(LOG_ERR, "Open log File%d Failed!%s", cid, strerror(errno));
        return; 
    }

    fwrite(log, len, 1, fd);
    fflush(fd);
    fclose(fd);
}

static void overheated_blinking(int cid)
{
	// block thread and blink led
	while (42) {
		mcompat_set_led(cid, LED_OFF);
		cgsleep_ms(500);
		mcompat_set_led(cid, LED_ON);
		cgsleep_ms(500);
	}
}

volatile int g_nonce_read_err = 0;

#define VAL_TO_TEMP(x)  ((double)((594 - x)* 5) / 7.5)
#define INC_PLL_TEMP	(95)	
#define DEC_PLL_TEMP	(105)
//#define HIGH_PLL		(1000)
//#define LOW_PLL			(900)
#define PLL_STEP		(100)

static double average(int *data, int size)
{
	int i;
	int count = 0;
	int total = 0;

	for (i = 0; i < size; i++)
	{
		if (data[i] > 0)
		{
			total += data[i];
			count++;
		}	    
	}

	return (double) total / count;
}

double get_average_volt(int chain_id, int chip_num)
{
	double volt_avg;
	int chip_volt[MCOMPAT_CONFIG_MAX_CHIP_NUM] = {0};
	
	mcompat_configure_tvsensor(chain_id, CMD_ADDR_BROADCAST, 0);
	usleep(1000);
	
	mcompat_get_chip_volt(chain_id, chip_volt);
	
	mcompat_configure_tvsensor(chain_id, CMD_ADDR_BROADCAST, 1);
	volt_avg = average(chip_volt, chip_num);
	return volt_avg;
}

void pll_config(struct A1_chain *a1, int target)
{
	//double volt_avg = get_average_volt(a1->chain_id, a1->num_active_chips);
	int cid = a1->chain_id;
	//vol change <= 2mv
	mcompat_chain_set_pll_by_step(cid, CMD_ADDR_BROADCAST, a1->pll, mcompat_chain_pll_to_level(target));
	//a1->vid = mcompat_find_chain_vid(a1->chain_id, a1->num_active_chips, CHIP_VID_DEF, volt_avg);
}

void overheat_ctl(double temp, struct A1_chain *a1)
{
	int cid = a1->chain_id;

	if(temp == 0)
		return;
	if(opt_A1Pll1 < PLL_STEP)
		return;
	
	if((temp >= DEC_PLL_TEMP)&&(a1->pll > mcompat_chain_pll_to_level(opt_A1Pll1 - PLL_STEP)))
	{
		
		//applog(LOG_NOTICE, "dec pll: %d", a1->chain_id);
		//dec pll 100M
		pll_config(a1, opt_A1Pll1 - PLL_STEP);
	}
	else if((temp <= INC_PLL_TEMP)&&(a1->pll < mcompat_chain_pll_to_level(opt_A1Pll1)))
	{
	
		//applog(LOG_NOTICE, "inc pll: %d", a1->chain_id);
		//inc pll to work pll
		pll_config(a1, opt_A1Pll1);
	}
}

#define MAX_CMD_FAILS		(0)
#define MAX_CMD_RESETS		(50)

static int g_cmd_fails[ASIC_CHAIN_NUM];
static int g_cmd_resets[ASIC_CHAIN_NUM];

static int64_t coinflex_scanwork(struct thr_info *thr)
{
    int i;
    uint8_t reg[128];
    struct cgpu_info *cgpu = thr->cgpu;
    struct A1_chain *a1 = cgpu->device_data;
    int32_t nonce_ranges_processed = 0;
	struct A1_chip *chip;
	int64_t hashes = 0;

    uint32_t nonce;
    uint8_t chip_id;
    uint8_t job_id;
    bool work_updated = false;
	struct timeval now;
	
    if (a1->num_cores == 0) {
        cgpu->deven = DEV_DISABLED;
        return 0;
    }

    mutex_lock(&a1->lock);
    int cid = a1->chain_id;

    if (a1->last_temp_time + TEMP_UPDATE_INT_MS < get_current_ms())
    {
        show_log[cid]++;
        check_disbale_flag[cid]++;

        cgpu->chip_num = a1->num_active_chips;
        cgpu->core_num = a1->num_cores;

        //printf("volShowLog[%d]=%s",cid,volShowLog[cid]);

        b52_log_print(cid, szShowLog[cid], sizeof(szShowLog[0]));

        a1->last_temp_time = get_current_ms();
    }

	/* We start with low diff to increase hashrate
	 * resolution reported and then increase diff after an hour to decrease
	 * load. */
	cgtime(&now);
	if (cgpu->drv->max_diff < DIFF_RUN) {
		int hours;

		hours = tdiff(&now, &cgpu->dev_start_tv) / 3600;
		if (hours > 8)
			cgpu->drv->max_diff = DIFF_RUN;
		else if (hours > 4 && cgpu->drv->max_diff < DIFF_4HR)
			cgpu->drv->max_diff = DIFF_4HR;
		else if (hours > 1 && cgpu->drv->max_diff < DIFF_1HR)
			cgpu->drv->max_diff = DIFF_1HR;
	}


    /* poll queued results */
    while (true){
        if (!get_nonce(a1, (uint8_t*)&nonce, &chip_id, &job_id)){
            break;
        }

        work_updated = true;

		chip = &(a1->chips[chip_id-1]);
		if (nonce == chip->last_nonce) {
			applog(LOG_INFO, "%d: chip %d: duplicate nonce.", cid, chip_id);
			chip->dupes++;
			continue;
		}

		if (chip_id < 1 || chip_id > a1->num_active_chips) {
			applog(LOG_WARNING, "%d: wrong chip_id %d", cid, chip_id);
			continue;
		}

        if (job_id < 1 || job_id > 4){
            applog(LOG_WARNING, "%d: chip %d: result has wrong ""job_id %d", cid, chip_id, job_id);
            continue;
        }
		
		chip->last_nonce = nonce;

        struct A1_chip *chip = &a1->chips[chip_id - 1];
        struct work *work = chip->work[job_id - 1];
        if (work == NULL){
            /* already been flushed => stale */
            applog(LOG_WARNING, "%d: chip %d: stale nonce 0x%08x", cid, chip_id, nonce);
            chip->stales++;
            continue;
        }
        if (!submit_nonce(thr, work, nonce)){
            applog(LOG_WARNING, "%d: chip %d: invalid nonce 0x%08x", cid, chip_id, nonce);
            chip->hw_errors++;
            /* add a penalty of a full nonce range on HW errors */
            nonce_ranges_processed--;
            continue;
        }

        applog(LOG_INFO, "Got nonce for chain %d / chip %d / job_id %d", a1->chain_id, chip_id, job_id);

        chip->nonces_found++;
		hashes += work->device_diff;		
		a1->lastshare = now.tv_sec;
    }

#ifdef USE_AUTONONCE
    mcompat_cmd_auto_nonce(a1->chain_id, 0, REG_LENGTH);   // disable autononce
#endif

	if (unlikely(now.tv_sec - a1->lastshare > CHAIN_DEAD_TIME)) {
		applog(LOG_EMERG, "chain %d not producing shares for more than %d mins, shutting down.",
		       cid, CHAIN_DEAD_TIME / 60);
		// TODO: should restart current chain only
		/* Exit cgminer, allowing systemd watchdog to restart */
		for (i = 0; i < ASIC_CHAIN_NUM; ++i)
			mcompat_chain_power_down(cid);
		exit(1);
	}

    /* check for completed works */
    if(a1->work_start_delay > 0)
    {
        applog(LOG_INFO, "wait for pll stable");
        a1->work_start_delay--;
    }
    else
    {
    
		/* Clean spi buffer before read 0a reg */
		hub_spi_clean_chain(cid);
       // mcompat_cmd_reset_reg(cid);
        for (i = a1->num_active_chips; i > 0; i--)
        {
            if(mcompat_cmd_read_register(a1->chain_id, i, reg, REG_LENGTH))
            {
              struct A1_chip *chip = NULL;
              struct work *work = NULL;
			  
			  /* Clear counter */
			  g_cmd_fails[cid] = 0;
			  g_cmd_resets[cid] = 0;

              uint8_t qstate = reg[9] & 0x03;
              if (qstate != 0x03)
              {
                work_updated = true;
                if(qstate == 0x0){
                  chip = &a1->chips[i - 1];
                  work = wq_dequeue(&a1->active_wq);

                  if (work == NULL){
                      continue;
                  }

                  if (set_work(a1, i, work, 0))
                  {
                      nonce_ranges_processed++;
                      chip->nonce_ranges_done++;
                  }
                }

                  chip = &a1->chips[i - 1];
                  work = wq_dequeue(&a1->active_wq);

                  if (work == NULL){
                      continue;
                  }

                  if (set_work(a1, i, work, 0))
                  {
                      nonce_ranges_processed++;
                      chip->nonce_ranges_done++;
                  }
               }
            }
			else
			{
				g_cmd_fails[cid]++;
				if (g_cmd_fails[cid] > MAX_CMD_FAILS) {
					// TODO: replaced with mcompat_spi_reset()
					applog(LOG_ERR, "Chain %d reset spihub", cid);
					hub_spi_clean_chain(cid);
					g_cmd_resets[cid]++;
					if (g_cmd_resets[cid] > MAX_CMD_RESETS) {
						applog(LOG_ERR, "Chain %d is not working due to multiple resets. shutdown.",
						       cid);
						/* Exit cgminer, allowing systemd watchdog to
						 * restart */
							mcompat_chain_power_down_all();
							exit(1);
					}
				}
			}
         } 
    }

	/* Temperature control */
	int chain_temp_status = mcompat_tempctrl_update_chain_temp(cid);

	cgpu->temp_min = (double)g_chain_tmp[cid].tmp_lo;
	cgpu->temp_max = (double)g_chain_tmp[cid].tmp_hi;
	cgpu->temp	   = (double)g_chain_tmp[cid].tmp_avg;

	if (chain_temp_status == TEMP_SHUTDOWN) {
		// shut down chain
		applog(LOG_ERR, "DANGEROUS TEMPERATURE(%.0f): power down chain %d",
			cgpu->temp_max, cid);
		mcompat_chain_power_down(cid);
		cgpu->status = LIFE_DEAD;
		cgtime(&thr->sick);

		/* Function doesn't currently return */
		overheated_blinking(cid);
	}
	
	overheat_ctl(cgpu->temp_max, a1);
	
	/* read chip temperatures and voltages */
	if (g_debug_stats[cid]) {
		cgsleep_ms(1);
		get_temperatures(a1);
		get_voltages(a1);
		g_debug_stats[cid] = 0;
	}

#ifdef USE_AUTONONCE
    mcompat_cmd_auto_nonce(a1->chain_id, 1, REG_LENGTH);   // enable autononce
#endif
    mutex_unlock(&a1->lock);

    if (nonce_ranges_processed < 0){
        applog(LOG_INFO, "nonce_ranges_processed less than 0");
        nonce_ranges_processed = 0;
    }else{
        applog(LOG_DEBUG, "%d, nonces processed %d", cid, nonce_ranges_processed);
    }

    cgtime(&a1->tvScryptCurr);
    timersub(&a1->tvScryptCurr, &a1->tvScryptLast, &a1->tvScryptDiff);
    cgtime(&a1->tvScryptLast);

    /* in case of no progress, prevent busy looping */
    if (!work_updated) // after work updated, also delay 10ms
        cgsleep_ms(5);

    //return ((double)opt_A1Pll1*a1->tvScryptDiff.tv_usec /2) * (a1->num_cores);
	
	return hashes * 0x100000000ull;
}



static struct api_data *coinflex_api_stats(struct cgpu_info *cgpu)
{
    struct A1_chain *t1 = cgpu->device_data;
	int fan_speed = g_fan_cfg.fan_speed;
    unsigned long long int chipmap = 0;
    struct api_data *root = NULL;
	bool fake = false;
    char s[32];
    int i;
	
    t1->VidOptimal = true;
    t1->pllOptimal = true;
		
    ROOT_ADD_API(int, "Chain ID", t1->chain_id, false);
    ROOT_ADD_API(int, "Num chips", t1->num_chips, false);
    ROOT_ADD_API(int, "Num cores", t1->num_cores, false);
    ROOT_ADD_API(int, "Num active chips", t1->num_active_chips, false);
    ROOT_ADD_API(int, "Chain skew", t1->chain_skew, false);
    ROOT_ADD_API(double, "Temp max", cgpu->temp_max, false);
    ROOT_ADD_API(double, "Temp min", cgpu->temp_min, false);
   
    ROOT_ADD_API(int, "Fan duty", fan_speed, true);
//	ROOT_ADD_API(bool, "FanOptimal", g_fan_ctrl.optimal, false);
	ROOT_ADD_API(int, "iVid", t1->vid, false);
    ROOT_ADD_API(int, "PLL", t1->pll, false);
	ROOT_ADD_API(int, "Voltage Max", t1->volt_max, false);
	ROOT_ADD_API(int, "Voltage Min", t1->volt_min, false);
	ROOT_ADD_API(int, "Voltage Avg", t1->volt, false);
	ROOT_ADD_API(bool, "VidOptimal", t1->VidOptimal, false);
	ROOT_ADD_API(bool, "pllOptimal", t1->pllOptimal, false);
//	ROOT_ADD_API(bool, "VoltageBalanced", t1->voltagebalanced, false);
	ROOT_ADD_API(int, "Chain num", cgpu->chainNum, false);
	ROOT_ADD_API(double, "MHS av", cgpu->mhs_av, false);
	ROOT_ADD_API(bool, "Disabled", t1->disabled, false);
	ROOT_ADD_API(bool, "Throttled", fake, true);
	for (i = 0; i < t1->num_chips; i++) {
		if (!t1->chips[i].disabled)
			chipmap |= 1 << i;
	}
	sprintf(s, "%Lx", chipmap);
	ROOT_ADD_API(string, "Enabled chips", s[0], true);
	ROOT_ADD_API(double, "Temp", cgpu->temp, false);

	for (i = 0; i < t1->num_chips; i++) {
		sprintf(s, "%02d HW errors", i);
		ROOT_ADD_API(int, s, t1->chips[i].hw_errors, true);
		sprintf(s, "%02d Stales", i);
		ROOT_ADD_API(int, s, t1->chips[i].stales, true);
		sprintf(s, "%02d Duplicates", i);
		ROOT_ADD_API(int, s, t1->chips[i].dupes, true);
		sprintf(s, "%02d Nonces found", i);
		ROOT_ADD_API(int, s, t1->chips[i].nonces_found, true);
		sprintf(s, "%02d Nonce ranges", i);
		ROOT_ADD_API(int, s, t1->chips[i].nonce_ranges_done, true);
		sprintf(s, "%02d Cooldown", i);
		ROOT_ADD_API(int, s, t1->chips[i].cooldown_begin, true);
		sprintf(s, "%02d Fail count", i);
		ROOT_ADD_API(int, s, t1->chips[i].fail_count, true);
		sprintf(s, "%02d Fail reset", i);
		ROOT_ADD_API(int, s, t1->chips[i].fail_reset, true);
		sprintf(s, "%02d Temp", i);
		ROOT_ADD_API(int, s, t1->chips[i].temp, true);
		sprintf(s, "%02d nVol", i);
		ROOT_ADD_API(int, s, t1->chips[i].nVol, true);
//		sprintf(s, "%02d PLL", i);
//		ROOT_ADD_API(int, s, t1->chips[i].pll, true);
//		sprintf(s, "%02d pllOptimal", i);
//		ROOT_ADD_API(bool, s, t1->chips[i].pllOptimal, true);
	}
	return root;
}

static struct api_data *T1_api_debug(struct cgpu_info *cgpu)
{
	struct A1_chain *t1 = cgpu->device_data;
	int timeout = 1000;

	g_debug_stats[t1->chain_id] = 1;

	// Wait for g_debug_stats cleared or timeout
	while (g_debug_stats[t1->chain_id] && timeout) {
		timeout -= 10;
		cgsleep_ms(10);
	}

	return coinflex_api_stats(cgpu);
}

struct device_drv coinflex_drv = 
{
    .drv_id                 = DRIVER_coinflex,
    .dname                  = "HLT_Coinflex",
    .name                   = "HLT",
    .drv_ver                = COINFLEX_DRIVER_VER,
    .drv_date               = COINFLEX_DRIVER_DATE,
    .drv_detect             = coinflex_detect,
    .get_statline_before    = coinflex_get_statline_before,
    .queue_full             = coinflex_queue_full,
    .get_api_stats          = coinflex_api_stats,
    .get_api_debug			= T1_api_debug,
    .identify_device        = NULL,
    .set_device             = NULL,
    .thread_prepare         = NULL,
    .thread_shutdown        = NULL,
    .hw_reset               = NULL,
    .hash_work              = hash_queued_work,
    .update_work            = NULL,
    .flush_work             = coinflex_flush_work,          // new block detected or work restart 
    .scanwork               = coinflex_scanwork,            // scan hash
    .max_diff               = DIFF_DEF						//65536
};

