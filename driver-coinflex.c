
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

#include "asic_inno.h"
#include "asic_inno_clock.h"
#include "asic_inno_cmd.h"
#include "asic_inno_gpio.h"

//#include "inno_fan.h"
//#include "inno_led.h"

#include "im_temp.h"

#define WORK_SIZE               (80)
#define DEVICE_TARGET_SIZE      (32)
#define TARGET_POS              (80)
#define TARGET_SIZE             (4)
#define MINER_ID_POS            (84)
#define MINER_ID_SIZE           (1)
#define WORK_ID_POS         (85)
#define WORK_ID_SIZE            (1)
#define FIND_NONCE_SIZE     (6)             // For receive value from miner: 4-Bytes nonce, 1-Byte miner_id, 1-Byte work_id

#define REPLY_SIZE              (2)
#define BUF_SIZE                    (128)
#define CHECK_DISABLE_TIME  0

struct Test_bench Test_bench_Array[5]={
    {1100,  0,  0,  0},
    {1100,  0,  0,  0},
    {1100,  0,  0,  0},
    {1100,  0,  0,  0},
    {1100,  0,  0,  0},
};


struct A1_chain *chain[ASIC_CHAIN_NUM];

uint8_t A1Pll1=A5_PLL_CLOCK_400MHz;
static uint8_t A1Pll2=A5_PLL_CLOCK_400MHz;
static uint8_t A1Pll3=A5_PLL_CLOCK_400MHz;
static uint8_t A1Pll4=A5_PLL_CLOCK_400MHz;
static uint8_t A1Pll5=A5_PLL_CLOCK_400MHz;
static uint8_t A1Pll6=A5_PLL_CLOCK_400MHz;
//static uint8_t A1Pll7=A5_PLL_CLOCK_400MHz;
//static uint8_t A1Pll8=A5_PLL_CLOCK_400MHz;

/* FAN CTRL */
//inno_fan_temp_s g_fan_ctrl;
inno_reg_ctrl_t s_reg_ctrl;

c_chain_temp g_chain_temp[ASIC_CHAIN_NUM];

//extern im_fan_temp_s *fan_temp_ctrl;
//extern im_temp_s *tmp_ctrl;

static uint32_t show_log[ASIC_CHAIN_NUM];
static uint32_t update_temp[ASIC_CHAIN_NUM];
static uint32_t check_disbale_flag[ASIC_CHAIN_NUM];

#define STD_V          0.84

int spi_plug_status[ASIC_CHAIN_NUM] = {0};

char szShowLog[ASIC_CHAIN_NUM][ASIC_CHIP_NUM][256] = {0};
char volShowLog[ASIC_CHAIN_NUM][256] = {0};
int fan_level[8]={30,40,50,60,70,80,90,100};

hardware_version_e g_hwver;
inno_type_e g_type;
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

#ifdef CHIP_A12
    if (a1->active_wq.num_elems >= 2)
#else
    if (a1->active_wq.num_elems >= a1->num_active_chips * 2)
#endif
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

    im_chain_power_down(a1->chain_id);

    a1->chips = NULL;
    free(a1);
}

int  cfg_tsadc_divider(struct A1_chain *a1,uint32_t pll_clk)
{
   // uint8_t  cmd_return;
    uint32_t tsadc_divider_tmp;
    uint8_t  tsadc_divider;
    //cmd0d(0x0d00, 0x0250, 0xa006 | (BYPASS_AUXPLL<<6), 0x2800 | tsadc_divider, 0x0300, 0x0000, 0x0000, 0x0000)
    uint8_t  buffer[] = {0x02,0x50,0xa0,0x06,0x28,0x00,0x03,0x00,0x00,0x00,0x00,0x00,0x00,0x00};
    uint8_t  readbuf[32] = {0};
#ifdef MPW
    tsadc_divider_tmp = (pll_clk/2)*1000/256/650;
#else
    tsadc_divider_tmp = (pll_clk/2)*1000/16/650;
#endif
    tsadc_divider = (uint8_t)(tsadc_divider_tmp & 0xff);

    buffer[5] = 0x00 | tsadc_divider;

    if(!im_cmd_read_write_reg0d(a1->chain_id, ADDR_BROADCAST, buffer, REG_LENGTH, readbuf)){
        applog(LOG_WARNING, "#####Write t/v sensor Value Failed!\n");
    }else{
        applog(LOG_WARNING, "#####Write t/v sensor Value Success!\n");
    }
    return 0;
}

void chain_detect_reload(struct A1_chain *a1)
{
    int cid = a1->chain_id;

    int n_chips = im_cmd_bist_start(cid, ADDR_BROADCAST);
    if(likely(n_chips > 0) && likely(n_chips != 0xff)){
        a1->num_chips = n_chips;
    }

    applog(LOG_INFO, "[reload]%d: detected %d chips", cid, a1->num_chips);

    usleep(10000);

    if(!im_cmd_bist_collect(cid, ADDR_BROADCAST)){
        applog(LOG_NOTICE, "[reload]bist collect fail");
    }

    applog(LOG_NOTICE, "collect core success");
    applog(LOG_NOTICE, "%d:  A1 chip-chain detected", cid);
}

bool init_A1_chain_reload(struct A1_chain *a1, int chain_id)
{
    int i;
    uint8_t src_reg[REG_LENGTH] = {0};
    uint8_t reg[REG_LENGTH] = {0};
    uint8_t buffer[4] = {0};
    bool result;
   
    if(a1 == NULL){
        applog(LOG_INFO, "%d: chain not plugged", chain_id);
        return false;
    }

    applog(LOG_INFO, "%d: A1 init chain reload", chain_id);

#ifndef FPGA_DEBUG_MODE
//    result = im_cmd_resetbist(a1->chain_id, ADDR_BROADCAST, buffer);
//applog(LOG_INFO, "im_cmd_resetbist(): %d - %02X", result, buffer[0]);
//    sleep(1);

    //bist mask
//    im_cmd_read_register(a1->chain_id, 0x01, reg, REG_LENGTH);
//    memcpy(src_reg, reg, REG_LENGTH);
//    src_reg[7] = src_reg[7] | 0x10;
//    im_cmd_write_register(a1->chain_id, ADDR_BROADCAST, src_reg, REG_LENGTH);
//    usleep(200);
#endif

#ifndef FPGA_DEBUG_MODE
    im_set_spi_speed(a1->chain_id, SPI_SPEED_6250K);    // 4: 6250000
    usleep(100000);
#endif

    chain_detect_reload(a1);
    usleep(10000);

    if (a1->num_chips < 1){
        goto failure;
    }

    /* override max number of active chips if requested */
    a1->num_active_chips = a1->num_chips;
    if ((A1_config_options.override_chip_num > 0) && a1->num_chips > A1_config_options.override_chip_num){
        a1->num_active_chips = A1_config_options.override_chip_num;
        applog(LOG_WARNING, "%d: limiting chain to %d chips",a1->chain_id, a1->num_active_chips);
    }

    a1->chips = calloc(a1->num_active_chips, sizeof(struct A1_chip));
    assert (a1->chips != NULL);

    if (!im_cmd_bist_fix(a1->chain_id, ADDR_BROADCAST)){
        goto failure;
    }

    usleep(200);

#ifndef FPGA_DEBUG_MODE

    //configure for vsensor
    inno_configure_tvsensor(a1,ADDR_BROADCAST,0);
    for (i = 0; i < a1->num_active_chips; i++){
        inno_check_voltage(a1, i+1, &s_reg_ctrl);
    } 

    //configure for tsensor
    inno_configure_tvsensor(a1,ADDR_BROADCAST,1);
    inno_get_voltage_stats(a1, &s_reg_ctrl);
    sprintf(volShowLog[a1->chain_id], "+         %2d  |  %8f  |  %8f  |  %8f  |\n",a1->chain_id,   \
        s_reg_ctrl.highest_vol[a1->chain_id],s_reg_ctrl.avarge_vol[a1->chain_id],s_reg_ctrl.lowest_vol[a1->chain_id]);

    inno_log_record(a1->chain_id, volShowLog[a1->chain_id], strlen(volShowLog[0]));
#endif

    for (i = 0; i < a1->num_active_chips; i++){
        check_chip(a1, i);
/*
#ifndef FPGA_DEBUG_MODE
        inno_fan_temp_add(&g_fan_ctrl, chain_id, i+1, a1->chips[i].temp);
#endif
*/
    }
/*
#ifndef FPGA_DEBUG_MODE
    chain_temp_update(&g_fan_ctrl,chain_id, g_type);
#endif

    //inno_fan_speed_update(&g_fan_ctrl,fan_level);

    applog(LOG_ERR, "[chain_ID]: Temp:%d\n",g_fan_ctrl.temp_highest[chain_id]);

#ifndef FPGA_DEBUG_MODE
    if(g_fan_ctrl.temp_highest[chain_id] < DANGEROUS_TMP){
        //im_chain_power_down(a1->chain_id);
        goto failure;
        //early_quit(1,"Notice Chain %d temp:%d Maybe Has Some Problem in Temperate\n",a1->chain_id,s_fan_ctrl.temp_highest[chain_id]);
    }
#endif
*/
    applog(LOG_ERR, "[chain_ID:%d]: Found %d Chips With Total %d Active Cores",a1->chain_id, a1->num_active_chips, a1->num_cores);

    return true;

failure:
    exit_A1_chain(a1);
    return false;
}

struct A1_chain *init_A1_chain(int chain_id)
{
    //int i;
    struct A1_chain *a1 = malloc(sizeof(*a1)); 
    assert(a1 != NULL);
    memset(a1,0,sizeof(struct A1_chain));

    applog(LOG_INFO, "%d: A1 init chain", chain_id);

    memset(a1, 0, sizeof(*a1));
    a1->chain_id = chain_id;

    a1->num_chips = chain_detect(a1);
    if (a1->num_chips < 1){
        applog(LOG_ERR, "bist start fail");
        goto failure;
    }
    applog(LOG_INFO, "%d: detected %d chips", a1->chain_id, a1->num_chips);
    
    usleep(100000);
    //sleep(10);
#ifndef FPGA_DEBUG_MODE
    cfg_tsadc_divider(a1, CHIP_PLL_DEF);// PLL_Clk_12Mhz[A1Pll1].speedMHz);	
#endif

    /* override max number of active chips if requested */
    a1->num_active_chips = a1->num_chips;
    if ((A1_config_options.override_chip_num > 0) && a1->num_chips > A1_config_options.override_chip_num){
        a1->num_active_chips = A1_config_options.override_chip_num;
        applog(LOG_WARNING, "%d: limiting chain to %d chips",a1->chain_id, a1->num_active_chips);
    }

    a1->chips = calloc(a1->num_active_chips, sizeof(struct A1_chip));
    assert (a1->chips != NULL);

    usleep(200000);

    applog(LOG_WARNING, "[chain_ID:%d]: Found %d Chips",a1->chain_id, a1->num_active_chips);

    mutex_init(&a1->lock);
    INIT_LIST_HEAD(&a1->active_wq.head);

    return a1;

failure:
    exit_A1_chain(a1);
    return NULL;
}
/*
static int prepll_chip_temp(struct A1_chain *a1)
{
    int i;
    uint8_t reg[REG_LENGTH];
    int cid = a1->chain_id;
    int temp;
    memset(reg,0,sizeof(reg));

    //while(s_fan_ctrl.temp_highest[cid] > 505)//FAN_FIRST_STAGE)
    for (i = a1->num_active_chips; i > 0; i --)
    { 
        if (!im_cmd_read_register(a1->chain_id, i, reg, REG_LENGTH))
        {
            applog(LOG_ERR, "%d: Failed to read temperature sensor register for chip %d ", a1->chain_id, i);

            continue;
        }

        temp = 0x000003ff & ((reg[7] << 8) | reg[8]);
        //applog(LOG_ERR,"cid %d,chip %d,temp %d\n",cid, i, temp);
        inno_fan_temp_add(&g_fan_ctrl, cid, i, temp);
    } 

    chain_temp_update(&g_fan_ctrl,cid,g_type);

    return 0;

}
*/
int inno_preinit(uint32_t pll, uint32_t last_pll, int *rst)
{ 
    int i;
    int timeout[ASIC_CHAIN_NUM] = { 0 };
    uint32_t temp_state[ASIC_CHAIN_NUM] = { 0 };

    int cur_pll[ASIC_CHAIN_NUM] = {0};
    int pll_lv1 = A1_ConfigA1PLLClock(last_pll);
    int pll_lv2 = A1_ConfigA1PLLClock(pll);

    usleep(500000);     // 500 ms

    for(i = 0; i < ASIC_CHAIN_NUM; i++)
    {
        if((chain[i] == NULL) || (!chain_flag[i]))
            continue;

        // init temperature
//        usleep(100000);
//        prepll_chip_temp(chain[i]);
        temp_state[i] = im_temp_ctrl(i, &g_chain_temp[i]);

        // init current pll
        cur_pll[i] = pll_lv1;
        // init result
        rst[i] = 1;
    }

    usleep(100000);     // 100 ms

    // rise pll from pll_lv1 to pll_lv2
    int finished = 0;
    while(!finished)
    {
        finished = 1;
        for(i = 0; i < ASIC_CHAIN_NUM; i++)
        {
            if((chain[i] == NULL) || (!chain_flag[i]))
                continue;

            // rise pll step by step
            if(rst[i] && cur_pll[i] <= pll_lv2)
            {
                if(set_chain_pll(i, cur_pll[i]))
                {
//                    applog(LOG_ERR, "chain%d PLL set to lv.%d", i, cur_pll[i]);
                    cur_pll[i]++;
                    timeout[i] = 0;     // reset timeout counter
                }
                else
                {
                    applog(LOG_ERR, "failed to set chain%d PLL to lv.%d", i, cur_pll[i]);
//                    if(timeout[i] < 5 
//                        && (g_fan_ctrl.temp_highest[i] > DANGEROUS_TMP) // higher temp value represents lower temperature
//                        && (g_fan_ctrl.temp_lowest[i] < START_FAN_TH))
                    if(timeout[i] < 5 && TEMP_NORMAL == temp_state[i])
//                    if(timeout[i] < 5)
                    {
                        timeout[i]++;
                        sleep(5);       // wait for 5 sec and try again
                    }
                    else
                    {
                        rst[i] = 0;     // failed
                    }
                }
            }

            // has finished?
            if(rst[i] && cur_pll[i] <= pll_lv2)
                finished = 0;
        }
        
        usleep(50000);  // 50 ms
    }

    usleep(100000);     // 100 ms

out_cfgpll:
//    inno_fan_speed_update(&g_fan_ctrl);

    return 0;
}

static int inc_pll(void)
{
    uint32_t i = 0,j = 0; 
    uint32_t last_pll = 0;
    int rst_pll[ASIC_CHAIN_NUM] = {0};

    applog(LOG_ERR, "pre init_pll...");
    for(i = PLL_Clk_12Mhz[0].speedMHz; i < (opt_A1Pll1+100); i += 100)
    {      
        i = (i > opt_A1Pll1) ? opt_A1Pll1 : i;

        inno_preinit(i, last_pll, rst_pll);
        last_pll = i;

        for(j = 0; j < ASIC_CHAIN_NUM; j++)
        {
            if (!rst_pll[j])
            {
                im_chain_power_down(j);
            }
            else
            {
                applog(LOG_ERR,"chain %d PLL set to %d", j, i);
            }
        }
    }

    return 0;
}

static void recfg_vid()
{
    int i, j;

    for(i = 0; i < ASIC_CHAIN_NUM; i++)
    {
        if((chain[i] == NULL) || (!chain_flag[i]))
        {
            continue;
        }
        // get chain vid
        chain[i]->vid = CHIP_VID_DEF;
        if(g_hwver == HARDWARE_VERSION_G9)
        {
            chain[i]->vid = opt_voltage1;
        }
        else if(g_hwver == HARDWARE_VERSION_G19)
        {
            switch(i)
            {
               case 0: chain[i]->vid = opt_voltage1; break;
               case 1: chain[i]->vid = opt_voltage2; break;
               case 2: chain[i]->vid = opt_voltage3; break;
               case 3: chain[i]->vid = opt_voltage4; break;
               case 4: chain[i]->vid = opt_voltage5; break;
               case 5: chain[i]->vid = opt_voltage6; break;
               case 6: chain[i]->vid = opt_voltage7; break;
               case 7: chain[i]->vid = opt_voltage8; break;
            }
        }
        // set vid step by step
        if(opt_voltage1 > CHIP_VID_DEF)
        {
            for(j = CHIP_VID_DEF + 1; j <= opt_voltage1; j++)
            {
                applog(LOG_ERR,"im_set_vid(chain=%d, vid=%d)\n", i, j);
                im_set_vid(i, j);
                usleep(500000);
            }
        }
        else if(opt_voltage1 < CHIP_VID_DEF)
        {
            for(j = CHIP_VID_DEF - 1; j >= opt_voltage1; j--)
            {
                applog(LOG_ERR,"im_set_vid(chain=%d, vid=%d)\n", i, j);
                im_set_vid(i, j);
                usleep(500000);
            }
        }
    }
}

static bool detect_A1_chain(void)
{
    int i,ret,res = 0;
    uint8_t buffer[4] = {0};

    for(i = 0; i < ASIC_CHAIN_NUM; i++){    
        if(im_get_plug(i) != 0)
        {
            applog(LOG_ERR, "chain %d power on fail", i);
            chain[i] = NULL;
            chain_flag[i] = 0;
            continue;
        }

        im_set_vid(i, CHIP_VID_DEF);            // init vid
        im_set_spi_speed(i, SPI_SPEED_390K);    // init spi speed
        usleep(10000);

        chain[i] = init_A1_chain(i);
        if (chain[i] == NULL){
            applog(LOG_ERR, "init chain %d fail", i);
            chain_flag[i] = 0;
            continue;
        } else {
            res++;
            chain_flag[i] = 1;
        }
#ifndef FPGA_DEBUG_MODE
        if(!im_cmd_resetall(i, ADDR_BROADCAST, buffer))
        {
            applog(LOG_ERR, "failed to reset chain %d!", i);
        }
        if(CMD_TYPE_A12 != (buffer[0] & 0xf0))
        {
            applog(LOG_ERR, "incompatible chip type %02X for chain %d!", buffer[0] & 0xf0, i);
        }
#endif
        applog(LOG_WARNING, "Detected the %d A1 chain with %d chips",i, chain[i]->num_active_chips);
    }

    usleep(200000);

#ifndef FPGA_DEBUG_MODE
    inc_pll();
    recfg_vid();
#endif

    for(i = 0; i < ASIC_CHAIN_NUM; i++){
        ret = init_A1_chain_reload(chain[i], i);
        if (false == ret){
            applog(LOG_ERR, "reload init a1 chain%d fail",i);
            continue;
        }

        struct cgpu_info *cgpu = malloc(sizeof(*cgpu));
        assert(cgpu != NULL);

        memset(cgpu, 0, sizeof(*cgpu));
        cgpu->drv = &coinflex_drv;
        cgpu->name = "BitmineA1.SingleChain";
        cgpu->threads = 1;

        cgpu->device_data = chain[i];

        chain[i]->cgpu = cgpu;
        add_cgpu(cgpu);

        // led on
        im_set_led(chain[i]->chain_id, 0);

        applog(LOG_WARNING, "Detected the %d A1 chain with %d chips / %d cores",i, chain[i]->num_active_chips, chain[i]->num_cores);
    }

#ifndef FPGA_DEBUG_MODE
//    inno_fan_speed_update(&g_fan_ctrl);
#endif

    return (res == 0) ? false : true;
}

static void coinflex_detect(bool __maybe_unused hotplug)
{
    if (hotplug){
        return;
    }

    struct timeval test_tv;
    int j = 0;

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

    g_hwver = inno_get_hwver();
    g_type = inno_get_miner_type();

    // TODO: get correct hwver value to init platform
//    int drv_hwver = misc_get_board_version();
//    int drv_mtype = misc_get_miner_type();
    sys_platform_init(PLATFORM_ZYNQ_HUB_G19, -1, ASIC_CHAIN_NUM, ASIC_CHIP_NUM);
    sys_platform_debug_init(IM_LOG_ERR);

    memset(&s_reg_ctrl,0,sizeof(s_reg_ctrl));
//    memset(&g_fan_ctrl,0,sizeof(g_fan_ctrl));

#ifndef FPGA_DEBUG_MODE
    c_temp_cfg tmp_cfg;
    im_temp_get_defcfg(&tmp_cfg);
    // TODO: modify some cfg here
    im_temp_ctrl_init(&tmp_cfg);

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

    // chain poweron & reset
    im_chain_power_down_all();
    sleep(5);
    im_chain_power_on_all();

    applog(LOG_INFO, "start A1 detect");
    if(detect_A1_chain()){
        return;
    }

    applog(LOG_ERR, "No device dectected");

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
#if 1
    struct A1_chain *a1 = coinflex->device_data;
    int cid = a1->chain_id;
    //board_selector->select(cid);
    int i;
    uint8_t buffer[4] = {0};

    mutex_lock(&a1->lock);
    /* stop chips hashing current work */
    if (!abort_work(a1)) 
    {
        applog(LOG_ERR, "%d: failed to abort work in chip chain!", cid);
    }

#ifdef USE_AUTONONCE
    im_cmd_auto_nonce(a1->chain_id, 0, REG_LENGTH);   // disable autononce
#endif
    
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

        if(!im_cmd_resetjob(a1->chain_id, i+1, buffer))
        {
            applog(LOG_WARNING, "chip %d clear work failed", i);
            continue;
        }

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

#endif
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

void Inno_Log_Save(struct A1_chip *chip,int nChip,int nChain)
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

void inno_log_print(int cid, void* log, int len)
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

void inno_log_record(int cid, void* log, int len)
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
/*
void read_chip_temp(struct A1_chain *a1, struct cgpu_info *cgpu)
{
    int i;
    int cid = a1->chain_id;
    uint8_t reg[REG_LENGTH] = {0};

    for (i = a1->num_active_chips; i > 0; i--) 
    {
//        if (is_chip_disabled(a1, i))
//        {
//            applog(LOG_ERR, "chip %d is disabled.", i);
//            continue;
//        }
        if(!im_cmd_read_register(cid, i, reg, REG_LENGTH))
        {
            applog(LOG_ERR, "chip %d reg read failed.", i);
            continue;
        }
        else
        {
            uint32_t temp = 0x000003ff & ((reg[7] << 8) | reg[8]);
#ifndef FPGA_DEBUG_MODE
            inno_fan_temp_add(&g_fan_ctrl, cid, i, temp);
#endif
        }
    }

#ifndef FPGA_DEBUG_MODE
    chain_temp_update(&g_fan_ctrl, cid, g_type);
    //inno_fan_speed_update(&g_fan_ctrl,fan_level);

    applog(LOG_INFO,"cid %d,hi %d,lo:%d,av:%d\n",cid,g_fan_ctrl.temp_highest[cid],g_fan_ctrl.temp_lowest[cid],g_fan_ctrl.temp_arvarge[cid]);
#endif

    cgpu->temp = g_fan_ctrl.temp2float[cid][1];
    cgpu->temp_max = g_fan_ctrl.temp2float[cid][0];
    cgpu->temp_min = g_fan_ctrl.temp2float[cid][2];
    cgpu->fan_duty = g_fan_ctrl.speed;
    cgpu->pre_heat = a1->pre_heat;
    //printf("g_fan_ctrl: cid %d,chip %d, chip %d,hi %d\n",g_fan_ctrl.pre_warn[0],g_fan_ctrl.pre_warn[1],g_fan_ctrl.pre_warn[2],g_fan_ctrl.pre_warn[3]);
    memcpy(cgpu->temp_prewarn,g_fan_ctrl.pre_warn, 4*sizeof(int));
    //printf("cgpu: cid %d,chip %d, chip %d,hi %d\n",cgpu->temp_prewarn[0],cgpu->temp_prewarn[1],cgpu->temp_prewarn[2],cgpu->temp_prewarn[3]);

    cgpu->chip_num = a1->num_active_chips;
    cgpu->core_num = a1->num_cores;
}
*/

volatile int g_nonce_read_err = 0;
volatile int g_reg_read_err[ASIC_CHAIN_NUM] = { 0 };

static int64_t coinflex_scanwork(struct thr_info *thr)
{
    int i;
    uint8_t reg[REG_LENGTH + 64];
    struct cgpu_info *cgpu = thr->cgpu;
    struct A1_chain *a1 = cgpu->device_data;
    int32_t nonce_ranges_processed = 0;
    uint32_t temp_state;

    uint32_t nonce;
    uint8_t chip_id;
    uint8_t job_id;
    bool work_updated = false;

    if (a1->num_cores == 0) {
        cgpu->deven = DEV_DISABLED;
        return 0;
    }

    mutex_lock(&a1->lock);
    int cid = a1->chain_id;

#ifdef USE_RT_TEMP_CTRL
    if (a1->last_temp_time + TEMP_UPDATE_INT_MS < get_current_ms())
    {
        temp_state = im_temp_ctrl(cid, &g_chain_temp[cid]);
        if(TEMP_UNKNOWN != temp_state)
        {
//            applog(LOG_ERR, "chain%d - Tmax: %d, Tavg: %d", 
//                cid, g_chain_temp[cid].tmp_hi, g_chain_temp[cid].tmp_avg);
            cgpu->temp = (float)g_chain_temp[cid].tmp_avg;
            cgpu->temp_max = (float)g_chain_temp[cid].tmp_hi;
            cgpu->temp_min = (float)g_chain_temp[cid].tmp_lo;

            a1->last_temp_time = get_current_ms();

            // led blink while reaching dangerous temperature
            if(TEMP_DANGEROUS == temp_state)
                loop_blink_led(cid, -1);
        }

        // TODO: ???
//        cgpu->fan_duty = 100;
        cgpu->chip_num = a1->num_active_chips;
        cgpu->core_num = a1->num_cores;

        inno_log_print(cid, szShowLog[cid], sizeof(szShowLog[0]));
        show_log[cid]++;
    }
#endif

    /* poll queued results */
    while (true){
        if (!get_nonce(a1, (uint8_t*)&nonce, &chip_id, &job_id)){
            break;
        }

        work_updated = true;
        if (chip_id < 1 || chip_id > a1->num_active_chips) {
            applog(LOG_WARNING, "%d: wrong chip_id %d", cid, chip_id);
            g_nonce_read_err++;
            if (g_nonce_read_err > 100) {
                im_chain_power_down_all();
                applog(LOG_ERR, "!!!unable to read nonce, exit!!!");
                early_quit(1, "!!!unable to read nonce, exit!!!");
            }
            continue;
        }

        g_nonce_read_err = 0;
        
        if (job_id < 1 || job_id > 4){
            applog(LOG_WARNING, "%d: chip %d: result has wrong job_id %d", cid, chip_id, job_id);
            continue;
        }

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

        chip->nonces_found++;
    }

#ifdef USE_AUTONONCE
    im_cmd_auto_nonce(a1->chain_id, 0, REG_LENGTH);   // disable autononce
#endif

#ifndef FPGA_DEBUG_MODE
    // ����һ��chip�������
    if(im_cmd_read_register(a1->chain_id, ASIC_CHIP_NUM >> 2, reg, REG_LENGTH))
#else
    // ��һ��оƬ�������
    if(im_cmd_read_register(a1->chain_id, 1, reg, REG_LENGTH))
#endif
    {
//        uint8_t qstate = reg[9] & 0x01;
        uint8_t qstate = (reg[9] >> 1) & 0x01;  // use backup queue

        if (qstate != 0x01)
        {
            work_updated = true;

            struct work *work = wq_dequeue(&a1->active_wq);
            struct work *work_copy = NULL;

            if(work != NULL)
            {
                for (i = a1->num_active_chips; i > 0; i--) 
                {
                    struct A1_chip *chip = &a1->chips[i - 1];

                    work_copy = copy_work(work);
                    __add_queued(cgpu, work_copy);
                    if (set_work(a1, i, work_copy, 0))
                    {
                        nonce_ranges_processed++;
                        chip->nonce_ranges_done++;
                    }

                    if(show_log[cid] > 0)                   
                    {   
                        Inno_Log_Save(chip, i-1, cid);
                        if(i == 1)
                            show_log[cid] = 0; 
                    }
                }

                work_completed(cgpu, work);
            }
            else
            {
                applog(LOG_ERR, "Wait work queue...");
            }
        }
    }

    if (nonce_ranges_processed < 0){
        applog(LOG_INFO, "nonce_ranges_processed less than 0");
        nonce_ranges_processed = 0;
    }

    if (nonce_ranges_processed != 0) {
        applog(LOG_DEBUG, "%d, nonces processed %d", cid, nonce_ranges_processed);
    }

    /* in case of no progress, prevent busy looping */
//    if (!work_updated)
//        cgsleep_ms(5);
    
#ifdef USE_AUTONONCE
    im_cmd_auto_nonce(a1->chain_id, 1, REG_LENGTH);   // enable autononce
#endif

    mutex_unlock(&a1->lock);

    cgsleep_ms(5);

    cgtime(&a1->tvScryptCurr);
    timersub(&a1->tvScryptCurr, &a1->tvScryptLast, &a1->tvScryptDiff);
    cgtime(&a1->tvScryptLast);

    return ((double)opt_A1Pll1 * a1->tvScryptDiff.tv_usec / 2) * a1->num_cores;
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
    .get_api_stats          = NULL,
    .identify_device        = NULL,
    .set_device             = NULL,
    .thread_prepare         = NULL,
    .thread_shutdown        = NULL,
    .hw_reset               = NULL,
    .hash_work              = hash_queued_work,
    .update_work            = NULL,
    .flush_work             = coinflex_flush_work,          // new block detected or work restart 
    .scanwork               = coinflex_scanwork,            // scan hash
    .max_diff               = 65536
};

