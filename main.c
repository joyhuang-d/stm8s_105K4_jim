/* MAIN.C file
 * 
 * Copyright (c) 2002-2005 STMicroelectronics
 */
#include "stm8s.h"
#include "stm8s_conf.h"
#include "uart.h"
#include "rc522.h"
#include "lf_send.h"
#include <string.h>
#include <stdlib.h>


unsigned char RFFull = 0;
unsigned char RFBit;
unsigned char LL_w = 0;
unsigned char First_flag = 0;
unsigned char Buff_B[8];
unsigned char RF_UartSend[10];
unsigned char secure_key[10];
u8 RF_set=0;
unsigned char BitCount;
unsigned char Time_1ms = 0;

#define RF_LEN       64
const uint8_t Secret_Key[8] = {0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0};


void RF_Remote(uint8_t);

enum pke_oper_state {
    PKE_OPER_STA_POWER_OFF,
    PKE_OPER_STA_POWER_ON,
    PKE_OPER_STA_WAIT,
    PKE_OPER_STA_IDLE,
    PKE_OPER_STA_LEARN,
    PKE_OPER_STA_BUSY,
    PKE_OPER_STA_ERROR
};

volatile struct PKE_config {
    uint8_t key_num;
    uint8_t rc522_num;
    volatile uint8_t oper_state;
    volatile uint8_t power_event_flag;
    volatile uint8_t learn_event_flag;
} TJTW_PKE;

#define BR_LIGHT_ON()      GPIO_WriteHigh(GPIOD, GPIO_PIN_3)
#define BR_LIGHT_OFF()     GPIO_WriteLow(GPIOD, GPIO_PIN_3)

#define BZ_ON()      GPIO_WriteHigh(GPIOB, GPIO_PIN_1)
#define BZ_OFF()     GPIO_WriteLow(GPIOB, GPIO_PIN_1)

#define LP_RIGHT_ON()      GPIO_WriteHigh(GPIOB, GPIO_PIN_3)
#define LP_RIGHT_OFF()     GPIO_WriteLow(GPIOB, GPIO_PIN_3)

#define MOTOR2_ON()     GPIO_WriteHigh(GPIOC, GPIO_PIN_2)
#define MOTOR2_OFF()    GPIO_WriteLow(GPIOC, GPIO_PIN_2)

#define MOTOR1_ON()     GPIO_WriteHigh(GPIOB, GPIO_PIN_0)
#define MOTOR1_OFF()    GPIO_WriteLow(GPIOB, GPIO_PIN_0)

#define MOTOR_FWD()  do{MOTOR1_ON(); MOTOR2_OFF();}while(0)
#define MOTOR_REV()  do{MOTOR1_OFF(); MOTOR2_ON();}while(0)
#define MOTOR_STOP() do{MOTOR1_OFF(); MOTOR2_OFF();}while(0)

#define RF_DATA_LOW()        (GPIO_ReadInputPin(GPIOD, GPIO_PIN_0) == RESET)   //RESET=0

#define KEY_BLOCK_SIZE       16    // 4 (RFID) + 8 (full Buff_B, include CRC) + 2 (wake up)
#define MAX_KEY_NUM          3
#define KEY_DATA_START_ADDR  0x00004110
#define KEY_COUNT_ADDR       0x00004100

//for ign to count down by 10s
#define IGN_TIMEOUT_MS      10000UL
#define IGN_TIMEOUT_S       (IGN_TIMEOUT_MS / 1000UL)
#define IGN_IS_ON()         (GPIO_ReadInputPin(GPIOB, GPIO_PIN_5) != RESET)  //SET=1
#define IGN_detect()         GPIO_ReadInputPin(GPIOB, GPIO_PIN_5)

#define MCU_REG_NUM      26

#define RX_WINDOW_LOOPS      160   /* Wait time per attempt = RX_WINDOW_LOOPS * 2ms */
#define ATTEMPTS_PER_VISIT   2     /* Retries per key before rotating */
#define SEARCH_ROUNDS        3     /* run 3 round */

#define WAIT_POLL_INTERVAL_MS   50U   /* Poll ignition state every 50ms */

/* Key cache in RAM (loaded from EEPROM before halt) */
uint8_t cached_key_count = 0;
uint8_t cached_keys[MAX_KEY_NUM][16];  // 5 x 16 bytes

const uint8_t mcu_user_config[MCU_REG_NUM] =
{
    0xA5,0x5A,0x01,0x7D,0x80,0x00,0x00,0x01,
    0xC3,0x3A,0x0C,0x01,0x00,0x15,0x00,0x01,
    0x01,0x81,0x32,0x00,0x00,0x00,0x00,0x00,
    0x00,0x00,
};

u8 Tx_Buffer[] = "RFID---test";
#define  BufferSize (countof(Tx_Buffer)-1)

uint16_t Calculate_CRC16(uint8_t *ptr, uint8_t len, uint8_t ran) {
    uint16_t crc = 0xFFFF;
    uint8_t i, j;
    if (ran == 1)
        crc = 0xFFFF;
    else if (ran == 2)
        crc = 0x1234;

    for (i = 0; i < len; i++) {
        crc ^= (uint16_t)ptr[i] << 8;
        for (j = 0; j < 8; j++) {
            if (crc & 0x8000) {
                crc = (crc << 1) ^ 0x1021;
            } else {
                crc <<= 1;
            }
        }
    }
    return crc;
}

uint16_t Generate_Wakeup_Code(uint8_t *data, uint8_t len) {
    uint16_t code = 0xA5A5;
    uint8_t i;

    for (i = 0; i < len; i++) {
        code ^= (uint16_t)data[i] + 0x9B;
        code = (uint16_t)((code << 7) | (code >> 9));
        code += (uint16_t)(data[i] ^ (code >> 8));
    }

    code ^= 0x5A5A;
    return code;
}

static void seed_random_generator(void) {
    uint16_t seed;

    seed = ((uint16_t)TIM2->CNTRH << 8) | (uint16_t)TIM2->CNTRL;
    seed ^= ((uint16_t)TIM4->CNTR << 8);
    seed ^= ((uint16_t)Time_1ms << 4);
    seed ^= ((uint16_t)LL_w << 1);
    seed ^= (uint16_t)BitCount;

    if (seed == 0u) {
        seed = 0x1234u;
    }

    srand((unsigned int)seed);
}

static uint16_t generate_valid_rolling_counter(uint8_t wake_hi, uint8_t wake_lo) {
    uint16_t wake_code = ((uint16_t)wake_hi << 8) | (uint16_t)wake_lo;
    uint16_t candidate;

    do {
        candidate = (uint16_t)(((uint16_t)(rand() & 0x00FFu) << 8) |
                               (uint16_t)(rand() & 0x00FFu));
    } while ((candidate == 0x0000u) || (candidate == wake_code));

    return candidate;
}

static void xtea_encrypt_host(uint32_t *v0, uint32_t *v1, const uint32_t *k) {
    uint8_t i;
    uint32_t sum = 0;
    uint32_t delta = 0x9E3779B9;

    for (i = 0; i < 32; i++) {
        *v0 += (((*v1 << 4) ^ (*v1 >> 5)) + *v1) ^ (sum + k[sum & 3]);
        sum += delta;
        *v1 += (((*v0 << 4) ^ (*v0 >> 5)) + *v0) ^ (sum + k[(sum >> 11) & 3]);
    }
}

static void generate_pke_rf_packet_host(const uint8_t *secure_key8, uint16_t rolling_counter, uint8_t *output_packet) {
    uint32_t key[4];
    uint32_t data0, data1;
    uint16_t crc;

    key[0] = ((uint32_t)secure_key8[0] << 24) | ((uint32_t)secure_key8[1] << 16) |
             ((uint32_t)secure_key8[2] << 8)  | (uint32_t)secure_key8[3];
    key[1] = ((uint32_t)secure_key8[4] << 24) | ((uint32_t)secure_key8[5] << 16) | 0x5A5A;
    key[2] = 0x5A5A5A5A;
    key[3] = 0x5A5A5A5A;

    data0 = (uint32_t)rolling_counter;
    data1 = 0x12345678;

    xtea_encrypt_host(&data0, &data1, key);

    output_packet[0] = (uint8_t)(data0 >> 24);
    output_packet[1] = (uint8_t)(data0 >> 16);
    output_packet[2] = (uint8_t)(data0 >> 8);
    output_packet[3] = (uint8_t)data0;
    output_packet[4] = (uint8_t)(data1 >> 24);
    output_packet[5] = (uint8_t)(data1 >> 16);

    crc = Calculate_CRC16(output_packet, 6, 2);
    output_packet[6] = (uint8_t)(crc >> 8);
    output_packet[7] = (uint8_t)(crc & 0xFF);
}

void Simple_Crypt(uint8_t *data, uint8_t len) {
    uint8_t i;
    for (i = 0; i < len; i++) {
        // 1. encrypt XOR with  Secret_Key
        data[i] ^= Secret_Key[i % 8];

        // 2. use not to increase complexity
        data[i] = ~data[i];

     // 3. (option) prevent consecutive identical characters.
        data[i] ^= i;
    }
}

void Clock_Config(void)
{
	
	//enable internal HSI clock(16MHZ)
	CLK_HSICmd(ENABLE);

	//make sure internal clock(HSI) is stable
	while (CLK_GetFlagStatus(CLK_FLAG_HSIRDY) == RESET);

	//set HSI DIV(High speed internal clock prescaler: 1)
	CLK_HSIPrescalerConfig(CLK_PRESCALER_HSIDIV1);
	CLK_PeripheralClockConfig(CLK_PERIPHERAL_SPI,   ENABLE);
    CLK_PeripheralClockConfig(CLK_PERIPHERAL_TIMER2, ENABLE);

}

void Clear_PKE_EEPROM(void)
{
    uint8_t i;

    FLASH_Unlock(FLASH_MEMTYPE_DATA);

    for (i = 0; i < 16; i++)
    {
        FLASH_ProgramByte(0x00004000 + i, 0x00);
    }

    FLASH_ProgramByte(0x00004100, 0x00);

    for (i = 0; i < 80; i++)
    {
        FLASH_ProgramByte(0x00004110 + i, 0x00);
    }

    FLASH_Lock(FLASH_MEMTYPE_DATA);
}

u8 Save_Combined_Key(uint8_t *rfid, uint8_t *rf433_full) {
    uint8_t num, i, k;
    uint16_t addr;
    uint8_t rfid_match, rf433_match,write_index;
    uint8_t existing_rfid[4];
    uint8_t existing_rf433[8];

    FLASH_Unlock(FLASH_MEMTYPE_DATA);
    num = FLASH_ReadByte(KEY_COUNT_ADDR);
    if (num > MAX_KEY_NUM)
        num = 0;

    // --- first : check exist or not ---
    for (i = 0; i < num; i++) {
        addr = KEY_DATA_START_ADDR + (i * KEY_BLOCK_SIZE);

        rfid_match = 1;
        rf433_match = 1;

        // check RFID is exist or not(4 bytes)
        for (k = 0; k < 4; k++) {
            if (FLASH_ReadByte(addr + k) != rfid[k]) {
                rfid_match = 0;
                break;
            }
        }

        // check 433M is exist or not (8 bytes, with CRC)
        for (k = 0; k < 8; k++) {
            if (FLASH_ReadByte(addr + 4 + k) != rf433_full[k]) {
                rf433_match = 0;
                break;
            }
        }

        // if any of them exist, abandon the write operation
        if (rfid_match || rf433_match) {
            UART2_SendStr("Key already exists! Skip saving.");
            FLASH_Lock(FLASH_MEMTYPE_DATA);
            return 1;
        }
    }

    // --- Part 2: Entry not found, proceed to write ---
    // Use circular buffer logic; wrap around to 0 if num reaches 3
    write_index = (num >= MAX_KEY_NUM) ? 0 : num;
    addr = KEY_DATA_START_ADDR + (write_index * KEY_BLOCK_SIZE);

    // Write RFID
    for (k = 0; k < 4; k++) {
        FLASH_ProgramByte(addr + k, rfid[k]);
    }
    // Write 433MHz payload (10 bytes incl. CRC)
    // Last 2 bytes: CRC of the 8-byte raw key, also used as the new wake-up code
    for (k = 0; k < 10; k++) {
        FLASH_ProgramByte(addr + 4 + k, rf433_full[k]);
    }

    // Update count (increment if not full, cap at MAX_KEY_NUM)
    if (num < MAX_KEY_NUM) {
        FLASH_ProgramByte(KEY_COUNT_ADDR, num + 1);
    }

    FLASH_Lock(FLASH_MEMTYPE_DATA);
    UART2_SendStr("New Key saved successfully.");
    return 0;
}


/* 20ms pulse */
static void motor_turn_on(void)
{
    MOTOR_FWD();
    Delay_ms(20);
    MOTOR_STOP();
}

static void motor_turn_off(void)
{
    MOTOR_REV();
    Delay_ms(20);
    MOTOR_STOP();
}

u8 Check_Combined_433M(uint8_t *target_rf433) {
    uint8_t i, k, match, num;
    uint16_t addr;

    FLASH_Unlock(FLASH_MEMTYPE_DATA);
    num = FLASH_ReadByte(KEY_COUNT_ADDR);
    if (num > MAX_KEY_NUM) num = MAX_KEY_NUM;

    for (i = 0; i < num; i++) {
        addr = KEY_DATA_START_ADDR + (i * KEY_BLOCK_SIZE);
        match = 1;
        // Compare 8 bytes starting at offset +4 (with CRC)
        for (k = 0; k < 8; k++) {
            if (FLASH_ReadByte(addr + 4 + k) != target_rf433[k]) {
                match = 0;
                break;
            }
        }
        if (match) {
            FLASH_Lock(FLASH_MEMTYPE_DATA);
            return 1;
        }
    }
    FLASH_Lock(FLASH_MEMTYPE_DATA);
    return 0;
}

u8 Check_Combined_RFID(uint8_t *target_rfid) {
    uint8_t i, k, match, num;
    uint16_t addr;

    FLASH_Unlock(FLASH_MEMTYPE_DATA);
    num = FLASH_ReadByte(KEY_COUNT_ADDR);
    if (num > MAX_KEY_NUM) num = MAX_KEY_NUM;

    for (i = 0; i < num; i++) {
        addr = KEY_DATA_START_ADDR + (i * KEY_BLOCK_SIZE);
        match = 1;
        // Compare 4 bytes starting at offset +0
        for (k = 0; k < 4; k++) {
            if (FLASH_ReadByte(addr + k) != target_rfid[k]) {
                match = 0;
                break;
            }
        }
        if (match) {
            FLASH_Lock(FLASH_MEMTYPE_DATA);
            return 1;
        }
    }
    FLASH_Lock(FLASH_MEMTYPE_DATA);
    return 0;
}

/* Load all keys from EEPROM to RAM cache before halt */
void Load_Keys_To_Cache(void) {
    uint8_t i, k;
    uint16_t addr;

    FLASH_Unlock(FLASH_MEMTYPE_DATA);

    /* Read key count */
    cached_key_count = FLASH_ReadByte(KEY_COUNT_ADDR);
    if (cached_key_count > MAX_KEY_NUM)
        cached_key_count = MAX_KEY_NUM;

    /* Load all keys (RFID + secure_key) to RAM */
    for (i = 0; i < cached_key_count; i++) {
        addr = KEY_DATA_START_ADDR + (i * KEY_BLOCK_SIZE);
        for (k = 0; k < KEY_BLOCK_SIZE; k++) {
            cached_keys[i][k] = FLASH_ReadByte(addr + k);
        }
    }

    FLASH_Lock(FLASH_MEMTYPE_DATA);
    UART2_SendStr("Keys loaded to RAM cache!");
}

/* Check 433M key against cached keys in RAM */
u8 Check_Combined_433M_Cached(uint8_t key_idx, uint8_t *target_rf433, uint16_t rolling_counter) {
    uint8_t k;
    uint8_t expected_packet[8];

    if (key_idx >= cached_key_count) {
        return 0;
    }

    /* cached_keys[key_idx][4..11] is secure key data (8 bytes) */
    generate_pke_rf_packet_host(&cached_keys[key_idx][4], rolling_counter, expected_packet);

    for (k = 0; k < 8; k++) {
        if (expected_packet[k] != target_rf433[k]) {
            return 0;
        }
    }
    return 1;
}

static void GPIO_Config(void)
{

    GPIO_Init(GPIOD, GPIO_PIN_3, GPIO_MODE_OUT_PP_LOW_FAST); /* D3 BR_LIGHT */
    GPIO_Init(GPIOB, GPIO_PIN_3, GPIO_MODE_OUT_PP_LOW_FAST); /* B3 LP_RIGHT */
    GPIO_Init(GPIOC, GPIO_PIN_2, GPIO_MODE_OUT_PP_LOW_FAST); /* Motor IN2 */
    GPIO_Init(GPIOB, GPIO_PIN_0, GPIO_MODE_OUT_PP_LOW_FAST); /* Motor IN1 */
    GPIO_Init(GPIOB, GPIO_PIN_1, GPIO_MODE_OUT_PP_LOW_FAST); /* BZ */

    GPIO_Init(GPIOB, GPIO_PIN_4, GPIO_MODE_IN_PU_IT);  //POWER KEY
    GPIO_Init(GPIOA, GPIO_PIN_2, GPIO_MODE_IN_FL_NO_IT); //LEARN KEY
    GPIO_Init(GPIOB, GPIO_PIN_5, GPIO_MODE_IN_FL_NO_IT); //IGN KEY

    GPIO_Init(GPIOD, GPIO_PIN_2, GPIO_MODE_OUT_PP_HIGH_FAST); //syn531 default disable
    GPIO_Init(GPIOD, GPIO_PIN_0, GPIO_MODE_IN_PU_NO_IT);    //RF DO
    GPIO_Init(GPIOE, GPIO_PIN_5, GPIO_MODE_OUT_PP_LOW_FAST);  //125k enable

    /* init gpio status */
    BR_LIGHT_OFF();
    LP_RIGHT_OFF();
    MOTOR_STOP();
    BZ_OFF();
    GPIO_WriteLow (GPIOD, GPIO_PIN_2);  //syn531 enable
}

/* ================= EXTI ================= */

static void EXTI_Config(void)
{
    /* PORTB rising edge */
    EXTI_SetExtIntSensitivity(EXTI_PORT_GPIOB,
                              EXTI_SENSITIVITY_RISE_ONLY);
}

/* ================= ISR ================= */

INTERRUPT_HANDLER(EXTI_PORTB_IRQHandler, 4)
{
    TJTW_PKE.power_event_flag = 1;
}

void TIM2_Init(void)
{
    TIM2_DeInit();
    TIM2_TimeBaseInit(TIM2_PRESCALER_16,100);   /* 0.1ms */
    TIM2_ITConfig(TIM2_IT_UPDATE , ENABLE);
    TIM2_OC2Init(TIM2_OCMODE_PWM1, TIM2_OUTPUTSTATE_ENABLE, 0, TIM2_OCPOLARITY_HIGH);
    TIM2_OC2PreloadConfig(ENABLE);
    TIM2_SetCounter(0x0000);
    TIM2_Cmd(ENABLE);
		/* TIM2 IRQ13 highest priority (level 0) */
		ITC->ISPR4 &= (uint8_t)(~0x0C);
}


void RF_Remote(uint8_t level)
{
    unsigned char i;
    const char hex_chars[] = "0123456789ABCDEF";
    char hex_out[4];
    uint16_t received_crc, calculated_crc, final_crc;
    disableInterrupts();
    RF_set = 0;
    for (i = 0; i < 8; i++) {
        RF_UartSend[i] = Buff_B[i];
    }
    received_crc = ((uint16_t)RF_UartSend[6] << 8) | (uint16_t)RF_UartSend[7];
    calculated_crc = Calculate_CRC16(RF_UartSend, 6,level);

    RFFull = 0;
    if (level == 2) {
        /* POWER_ON: key should return rolling packet with CRC only. */
        if (calculated_crc == received_crc ) {
            UART2_SendString("\r\nRF Data: ", 11);
            for (i = 0; i < 8; i++) {
                uint8_t val = RF_UartSend[i];
                hex_out[0] = hex_chars[(val >> 4) & 0x0F];
                hex_out[1] = hex_chars[val & 0x0F];
                hex_out[2] = ' ';
                UART2_SendString((unsigned char*)hex_out, 3);
            }
            RF_set = 1;
        } else {
            UART2_SendString("\r\nRF Data CRC Error in POWER_ON! ", 34);
        }
    } else if (calculated_crc == received_crc && RF_UartSend[0] == 0x54 && RF_UartSend[1] == 0x4A) {
        RF_set = 1;
        UART2_SendString("\r\nRF Data: ", 11);
        for (i = 0; i < 8; i++) {
            uint8_t val = RF_UartSend[i];
            hex_out[0] = hex_chars[(val >> 4) & 0x0F];
            hex_out[1] = hex_chars[val & 0x0F];
            hex_out[2] = ' ';
            UART2_SendString((unsigned char*)hex_out, 3);
        }
        if(level ==1) {
            calculated_crc = Generate_Wakeup_Code(RF_UartSend, 8);
            RF_UartSend[8] = (uint8_t)(calculated_crc >> 8);   // wake-up code high
            RF_UartSend[9] = (uint8_t)(calculated_crc & 0xFF); // wake-up code low
            memcpy(secure_key, RF_UartSend, 6);
            Simple_Crypt(secure_key, 6);
            final_crc = Calculate_CRC16(secure_key, 6, 2);
            secure_key[6] = (uint8_t)(final_crc >> 8);
            secure_key[7] = (uint8_t)(final_crc & 0xFF);
            secure_key[8] = (uint8_t)(calculated_crc >> 8);   // wake-up code high
            secure_key[9] = (uint8_t)(calculated_crc & 0xFF); // wake-up code low

        }

    } else {
        if (calculated_crc != received_crc) {
            UART2_SendString("\r\nRF Data CRC Error! ", 22);
        } else {
            UART2_SendString("\r\nRF Data Header Error! ", 23);
        }
    }
    enableInterrupts();
    UART2_SendString("\r\n", 2);
}


@far @interrupt void tim2_irqhandler(void)
{
    /* Clear TIM2 update interrupt flag */
    TIM2_ClearITPendingBit(TIM2_IT_UPDATE);

    /* -------------------------------------------------------------
     * Time base: 1 ms tick and 10 ms tick
     * ------------------------------------------------------------- */
    Time_1ms++;

    if (Time_1ms >= 10)
    {
        Time_1ms = 0;

        /* LF send timer countdown (clamp to 0) */
        if ((LF_ENABLE == 1) && (LF_Send_Tim > 0))
            LF_Send_Tim--;
        else
            LF_Send_Tim = 0;
    }

    /* If an RF frame is already captured, skip decoding */
    if (RFFull)
        return;

    /* -------------------------------------------------------------
     * RF OOK decoding:
     * - Measure LOW pulse width (LL_w) while RF_DATA is low
     * - On rising edge (LOW -> HIGH), interpret the LOW width
     * ------------------------------------------------------------- */
    if (RF_DATA_LOW())
    {
        /* Accumulate LOW width in ticks */
        LL_w++;
        RFBit = 0;   /* Mark current level as LOW */
    }
    else
    {
        /* Rising edge: process the LOW width that just ended */
        if (!RFBit)
        {
            if (!First_flag)
            {
                /* Detect sync/preamble LOW width */
               // if ((LL_w > 40) && (LL_w < 60))
							 if ((LL_w >= 35) && (LL_w <= 65)) // Relax the detection range of the sync header.
                {
                    First_flag = 1;
                    BitCount   = 0;
                    Buff_B[0] = Buff_B[1] = Buff_B[2] = 0;
                    Buff_B[3] = Buff_B[4] = Buff_B[5] = 0;
                    Buff_B[6] = Buff_B[7] = 0;
                }
            }
            else
            {
                /* Decode data bits by LOW width */
                //if ((LL_w > 3) && (LL_w <= 7))
								if ((LL_w >= 2) && (LL_w <= 7))  // Relax the lower limit of Bit 1 to 2 (enhance weak signal detection).
                {
                    /* Bit '1' */
                    if (BitCount < RF_LEN)
                    {
                        Buff_B[BitCount >> 3] <<= 1;
                        Buff_B[BitCount >> 3] |= 0x01;
                        BitCount++;
                    }
                }
                //else if ((LL_w >= 8) && (LL_w < 13))
								else if ((LL_w >= 8) && (LL_w <= 15)) // Relax the upper limit of Bit 0 to 15 (tolerate noise-extended waveforms)
                {
                    /* Bit '0' */
                    if (BitCount < RF_LEN)
                    {
                        Buff_B[BitCount >> 3] <<= 1;
                        BitCount++;
                    }
                }
                else
                {
                    /* Invalid width: reset decoder state */
                    First_flag = 0;
                    BitCount   = 0;
                }

                /* Frame complete */
                if (BitCount >= RF_LEN)
                {
                    BitCount   = 0;
                    First_flag = 0;
                    RFFull     = 1;
                }
            }

            /* Reset LOW width counter after processing */
            LL_w = 0;
        }

        RFBit = 1;   /* Mark current level as HIGH */
    }
}

void Handle_State_Wait(uint8_t *ign_wait)
{
    uint16_t elapsed_ms;               // Accumulated polling time in ms within a 1-second window

    UART2_SendStr("PKE_OPER_STA_WAIT in!");

    /* Check if Power Key is pressed; if so, immediately shut down to POWER_OFF */
    if (TJTW_PKE.power_event_flag) {
        TJTW_PKE.power_event_flag = 0;             // Clear power key trigger flag
        motor_turn_off();                           // Execute motor locking
        BR_LIGHT_OFF();                             // Turn off the light
        TJTW_PKE.oper_state = PKE_OPER_STA_POWER_OFF; // Transition to POWER_OFF state
        *ign_wait = 0;                                  // Exit WAIT state
        return;
    }

    if (IGN_IS_ON()) {
        /* Ignition ON: transition to IDLE */
        TJTW_PKE.oper_state = PKE_OPER_STA_IDLE;
        *ign_wait = 0;
        UART2_SendStr("IGN_ON PKE_OPER_STA_WAIT out!");
        return;
    } 

    elapsed_ms = 0;
    
    /* Poll for key/ignition events in slices across a 1-second window to maintain responsiveness */
    while (elapsed_ms < 1000U) {
        Delay_ms(WAIT_POLL_INTERVAL_MS);
        elapsed_ms += WAIT_POLL_INTERVAL_MS;

        if (TJTW_PKE.power_event_flag) {
            TJTW_PKE.power_event_flag = 0;
            motor_turn_off();
            BR_LIGHT_OFF();
            TJTW_PKE.oper_state = PKE_OPER_STA_POWER_OFF;
            *ign_wait = 0;
            return;
        }

        if (IGN_IS_ON()) {
            TJTW_PKE.oper_state = PKE_OPER_STA_IDLE;
            *ign_wait = 0;
            UART2_SendStr("IGN_ON PKE_OPER_STA_WAIT out!");
            return;
        }
    }

    (*ign_wait)++;

    if (*ign_wait >= IGN_TIMEOUT_S) {
        /* Timeout reached: return to POWER_OFF immediately on the 10th second */
        TJTW_PKE.oper_state = PKE_OPER_STA_POWER_OFF;
        *ign_wait = 0;
        motor_turn_off();
        UART2_SendStr("PKE_OPER_STA_WAIT out!");
    }
}


void Handle_State_Idle(int *idle)
{
    if (*idle == 0) {
        UART2_SendStr("PKE_OPER_STA_IDLE in!");
        *idle = 1;
        TIM2_CCxCmd(TIM2_CHANNEL_2, DISABLE);
    }

    /* Blue light indicator */
    BR_LIGHT_ON();

    /* Power Key press in IDLE state; clear flag only */
    if (TJTW_PKE.power_event_flag) {
        TJTW_PKE.power_event_flag = 0; // Clear flag without executing motor_turn_off() or state transition
        UART2_SendStr("Power Key pressed during IDLE, ignored!");
    } 
    
    /* Transition to POWER_OFF only when ignition switch (IGN) is manually turned OFF */
    if (!IGN_IS_ON()) {
        /* Ignition OFF event */
        motor_turn_off();
        TJTW_PKE.oper_state = PKE_OPER_STA_POWER_OFF;
        TIM2_CCxCmd(TIM2_CHANNEL_2, DISABLE);
        BR_LIGHT_OFF();
        UART2_SendStr("IGN_OFF PKE_OPER_STA_IDLE out!");
        *idle = 0;
    }
}

void Handle_State_Learn(void)
{
    int i;
    int ret = 0;
    uint8_t rfid_set = 0;
    unsigned char rc522_SN[4];

    UART2_SendStr("PKE_OPER_STA_LEARN in!");
    TIM2_Init();
    TIM2_CCxCmd(TIM2_CHANNEL_2, DISABLE);
    GPIO_Init(GPIOD, GPIO_PIN_3, GPIO_MODE_OUT_PP_LOW_FAST);
    enableInterrupts();

    /* Attempt to read RFID card for 25 iterations */
    for (i = 0; i < 25; i++) {
        LP_RIGHT_ON();  /* Red light */
        BR_LIGHT_ON();  /* Blue light */
        Delay_ms(100);
        showcard(Tx_Buffer, &rfid_set, rc522_SN);
        Reset_RC522();
        if (rfid_set == 1) {
            UART2_SendString(Tx_Buffer, 17);
            i = 50;  /* Exit loop */
        }
        LP_RIGHT_OFF();
        BR_LIGHT_OFF();
        Delay_ms(100);
    }

    if (rfid_set == 1) {
        /* RFID card detected, now learn 433M key */
        UART2_SendStr("433m key learned!");
        i = 0;
        while (i < 16) {
            BR_LIGHT_ON();  /* Blue light */
            LF_SendData(0xc3, 0x3a, PATTREN_BIT, LF_SEND_CH1, 0x01, 0x01);
            Delay_ms(100);
            BR_LIGHT_OFF();
            Delay_ms(150);
            if (RFFull) {
                RF_Remote(1);
                UART2_SendStr("Get 433m key!");
                BR_LIGHT_OFF();
                break;
            }
            i++;
        }

        if (RF_set == 1) {
            /* Both RFID and 433M keys received, save combined key */
            LF_SendData(0xc3, 0x3a, PATTREN_BIT, LF_SEND_CH1, RF_UartSend[8], RF_UartSend[9]);
            ret = Save_Combined_Key(rc522_SN, secure_key);
            if (ret > 0) {
                UART2_SendStr("Add 2 keys to eeprom failed!");
                LP_RIGHT_ON();
                Delay_ms(500);
                LP_RIGHT_OFF();
            } else {
                UART2_SendStr("Add 2 keys to eeprom!");
                Load_Keys_To_Cache();
            }
        } else {
            /* 433M key not received */
            UART2_SendStr("433m key not learned!");
            LP_RIGHT_ON();
            Delay_ms(500);
            LP_RIGHT_OFF();
        }
    } else {
        /* RFID card not detected */
        UART2_SendStr("RFID key not learned!");
        LP_RIGHT_ON();
        Delay_ms(500);
        LP_RIGHT_OFF();
    }

    RF_set = 0;
    TJTW_PKE.oper_state = PKE_OPER_STA_POWER_OFF;
    UART2_SendStr("PKE_OPER_STA_LEARN out!");
}

void Handle_State_Power_On(void)
{
    int i;
    int ret = 0;
    uint8_t rfid_set = 0;
    unsigned char rc522_SN[4];

    uint8_t round;
    uint8_t key_idx;
    uint8_t attempt;
    uint8_t rolling_hi;
    uint8_t rolling_lo;
    uint16_t rolling_counter;

    UART2_SendStr("PKE_OPER_STA_POWER_ON in!");
    enableInterrupts();

    /* Step 1: Check RFID key (3 attempts) */
    UART2_SendStr("check RFID key!");
    for (i = 0; i < 3; i++) {
        Delay_ms(100);
        showcard(Tx_Buffer, &rfid_set, rc522_SN);
        Reset_RC522();
        if (rfid_set == 1) {
            UART2_SendString(Tx_Buffer, 17);
            rfid_set = 0;
            i = 50;  /* Exit loop */
            ret = Check_Combined_RFID(rc522_SN);
        }
    }

    /* Step 2: If RFID not matched, check 433M key
     * round(3) -> key_idx(3) -> attempt(2)
     */
    if (ret == 0) {
        UART2_SendStr("Check 433m key !");

        for (round = 0; round < SEARCH_ROUNDS && ret == 0; round++) {

            for (key_idx = 0; key_idx < cached_key_count && ret == 0; key_idx++) {

                for (attempt = 0; attempt < ATTEMPTS_PER_VISIT && ret == 0; attempt++) {

                    disableInterrupts();
                    RF_set = 0;
                    RFFull = 0;
                    First_flag = 0;
                    BitCount = 0;
                    memset(Buff_B, 0, sizeof(Buff_B));
                    enableInterrupts();

                    rolling_counter = generate_valid_rolling_counter(
                                           cached_keys[key_idx][12],
                                           cached_keys[key_idx][13]);
                    rolling_hi = (uint8_t)(rolling_counter >> 8);
                    rolling_lo = (uint8_t)(rolling_counter & 0xFF);

                    /* Send LF command with wakeup code from cached key */
                    LF_SendData(cached_keys[key_idx][12], cached_keys[key_idx][13],
                                PATTREN_BIT, LF_SEND_CH1, rolling_hi, rolling_lo);

                    /* Wait for RF response (max 350ms) */
                    {
                        uint8_t delay_loop;
                        for (delay_loop = 0; delay_loop < RX_WINDOW_LOOPS; delay_loop++) {
                            Delay_ms(2);
                            if (RFFull) {
                                disableInterrupts();
                                break;
                            }
                        }
                    }

                    if (RFFull) {
                        RF_Remote(2);
                        if (RF_set && Check_Combined_433M_Cached(key_idx, RF_UartSend, rolling_counter)) {
                            UART2_SendStr("433m key matched!");
                            ret = 1;
                        } else {
                            if (RF_set) {
                                UART2_SendStr("433m rolling packet mismatch, retry...");
                            } else {
                                UART2_SendStr("433m RF CRC error, retry...");
                            }
                        }
                        RFFull = 0;
                    }

                } 
            } 
        } 

        enableInterrupts();
    }

    /* Step 3: Execute action based on validation result */
    if (ret == 1) {
        motor_turn_on();
        TJTW_PKE.oper_state = PKE_OPER_STA_WAIT;
    } else {
        LP_RIGHT_ON();
        TJTW_PKE.oper_state = PKE_OPER_STA_POWER_OFF;
        Delay_ms(500);
        LP_RIGHT_OFF();
    }

    UART2_SendStr("PKE_OPER_STA_POWER_ON out!");
}
void Handle_State_Power_Off(void)
{
    UART2_SendStr("PKE_OPER_STA_POWER_OFF in!");
    enableInterrupts();

    /* Stop motor and prepare for halt */
    MOTOR_STOP();
    Delay_ms(50);
    motor_turn_off();
    halt();
    Delay_ms(50);

    /* Reinitialize peripherals after wake-up */
    Clock_Config();
    GPIO_Config();
    TIM4_Init();
    Uart_Init();
    InitRc522();
    Delay_ms(50);

    /* Check wake-up source and set next state */
    if (TJTW_PKE.power_event_flag) {
        TJTW_PKE.power_event_flag = 0;
        Load_Keys_To_Cache();

        if (GPIO_ReadInputPin(GPIOA, GPIO_PIN_2)) {
            /* LEARN key pressed: enter LEARN mode */
            TJTW_PKE.oper_state = PKE_OPER_STA_LEARN;
        } else {
            /* Normal power-on: enter POWER_ON mode */
            TJTW_PKE.oper_state = PKE_OPER_STA_POWER_ON;
        }
    }

    Uart_Init();
    UART2_SendStr("PKE_OPER_STA_POWER_OFF out!");
}


void main()
{
    int idle;
    uint8_t cfg_idx;
    uint8_t ign_wait = 0;

    TJTW_PKE.oper_state = PKE_OPER_STA_POWER_OFF;
    TJTW_PKE.power_event_flag = 0;
    TJTW_PKE.learn_event_flag = 0;
    idle=0;

    Clock_Config();
    GPIO_Config();
    EXTI_Config();
    TIM4_DeInit();
    TIM4_Init();
	//MX_TIM4_Init();
    Uart_Init();
    InitRc522();
    Delay_ms(100);
    //TIM2_PWM_Config();
    //Clear_PKE_EEPROM();

    LF_ClockOccurs(125);
    for (cfg_idx = 0; cfg_idx < MCU_REG_NUM; cfg_idx++) {
        Set_Buff[cfg_idx] = mcu_user_config[cfg_idx];
    }
    LF_PLL_SET(LF_PLL);

    Delay_InIt(16);
    TIM2_Init();   //need ro mask  TIM2_PWM_Config()
    enableInterrupts();
    seed_random_generator();
    /* Load all keys to RAM cache before entering main loop */
    Load_Keys_To_Cache();
		
    UART2_SendStr("system start!");
		
    while(1)
    {
        // LF_SendData(PATTERN1,PATTERN2,PATTREN_BIT,LF_SEND_CH1);
        // Delay_ms(250);
        // if (RFFull) {
        //     RF_Remote();
        // }
       
        switch(TJTW_PKE.oper_state) {
            case PKE_OPER_STA_POWER_OFF:
                Handle_State_Power_Off();
                break;
            case PKE_OPER_STA_POWER_ON:
                Handle_State_Power_On();
                break;
            case PKE_OPER_STA_WAIT:
                Handle_State_Wait(&ign_wait);
                break;
            case PKE_OPER_STA_IDLE:
                Handle_State_Idle(&idle);
                break;
            case PKE_OPER_STA_LEARN:
                Handle_State_Learn();
                break;
            default:
                UART2_SendStr("Default state");
                TJTW_PKE.oper_state = PKE_OPER_STA_POWER_OFF;
                break;
        }

    }
}
