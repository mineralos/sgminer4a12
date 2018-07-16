#ifndef _ASIC_B52_CMD_
#define _ASIC_B52_CMD_

#include <pthread.h>
#include <sys/time.h>

#include "asic_b52.h"

#define CMD_TYPE_A7         0xb0
#define CMD_TYPE_A8         0x30
#define CMD_TYPE_A11        0x70
#define CMD_TYPE_A12        0xc0


#define ADDR_BROADCAST      0x00

#define LEN_BIST_START      4
#define LEN_BIST_COLLECT    4
#define LEN_BIST_FIX        4
#define LEN_RESET           6
#define LEN_WRITE_JOB       92
#define LEN_READ_RESULT     10
#define LEN_WRITE_REG       18
#define LEN_READ_REG        12


#define SPI_REC_DATA_LOOP   10
#define SPI_REC_DATA_DELAY  1

#define ASIC_RESULT_LEN     6
#define READ_RESULT_LEN     (ASIC_RESULT_LEN + 2)

struct Test_bench {
    uint32_t uiPll; 
    int uiVol;
    uint32_t uiScore;
    uint32_t uiCoreNum;
};

#define WORK_BUSY 0
#define WORK_FREE 1


uint16_t CRC16_2(unsigned char* pchMsg, unsigned short wDataLen);

//void flush_spi(struct A1_chain *pChain);
void hexdump_error(char *prefix, uint8_t *buff, int len);
void hexdump(char *prefix, uint8_t *buff, int len);


#endif
