/* Portions taken from
 * https://github.com/trezor/trezor-firmware/
 * Specifically, these two files:
 * trezor-firmware/core/embed/io/power_manager/npm1300/npm1300.c
 * trezor-firmware/core/embed/io/power_manager/inc/io/pmic.h
 */

// #include <stdint.h>
// #include <stdio.h>
// #include <math.h>

/* An example PMIC (power-managment integrated circuit)
 * In this case we can conceptually think of this as a 4-dimensional vector
 * with 2 ignored elements */
typedef struct {
  float vbat; // Battery voltage [V]
  float vsys; // System voltage [V]
  // Battery current [mA]
  // - positive value means discharging
  // - negative value means charging
  float ibat;
  float ntc_temp; // NTC (negative temperature coefficient) temperature [°C]
//  bool ntc_disconnected; // NTC disconnection flag
//  unsigned char status; // for debugging in some other routine)
} pmic_report_t;

/* Note: ntc_adc is from an analog to digital converter so we expect to have a
 * restricted set of valid values */
// float set_ntc_temp(pmic_report_t *r, float ntc_adc)
// {
// 	float beta = 3380.0;
// 	r->ntc_temp = 
// 			1 / (1 / 298.15 - (1 / beta) * logf(1024.0 / ntc_adc - 1)) - 298.15 +
// 			25.0;
// 	return r->ntc_temp;
// }

/*@
   requires 0.0 <= vbat_adc <= 65535.0;
*/
// float calc_ntc_temp(float ntc_adc)
// {
// 	float beta = 3380.0;
// 	return 1 / (1 / 298.15 - (1 / beta) * logf(1024.0 / ntc_adc - 1)) - 298.15 +
// 			25.0;
// }

/* TODO: Get working for all float datatypes */
/* vbat_adc is converted from uint16_t
 * So a follow-up question: what is the uncertainty? There is really only 16 bits of
 * precision here, maximum, and probably less depending on ADC model. */
/*@
   requires 0.0f <= vbat_adc <= 65535.0f;
*/
float calc_vbat(float vbat_adc)
{
	// Calculate the battery voltage (VBAT) from the ADC value.
	// VBAT is scaled by the voltage divider ratio and ADC resolution.
	return (vbat_adc * 5.0f) / 1023.0f;
}

/*@
   requires 0.0f <= vsys_adc <= 65535.0f;
*/
float calc_vsys(float vsys_adc)
{
	// Calculate the system voltage (VSYS) from the ADC value.
	// VSYS is scaled based on the system voltage divider ratio and ADC
	// resolution.
	return (vsys_adc * 6.375f) / 1023.0f;
}

/*@
   requires 0.0f <= vsys_adc <= 65535.0f;
*/
// float fill_vsys(pmic_report_t *report, float vsys_adc)
// {
// 	// Calculate the system voltage (VSYS) from the ADC value.
// 	// VSYS is scaled based on the system voltage divider ratio and ADC
// 	// resolution.
// 	report->vsys = (vsys_adc * 6.375f) / 1023.0f;
// 	return report->vsys;
// }

// void set_charging(pmic_report_t *report, bool charging, float ibat_adc)
// {
//   if (ibat_charging) {
//     report->ibat = ((int)ibat_adc * drv->i_limit) / 1250.0;
//   } else {
//     report->ibat = -((int)ibat_adc * drv->i_charge) / 800.0;
//   } else {
//     report->ibat = 0;
//   }
// }

// int main()
// {
// 	int counter = 0;
// 	pmic_report_t r;
// 	for (uint16_t ntc_adc=0; ntc_adc < 65535; ntc_adc++) {
// 		calc_ntc_temp((float) ntc_adc);
// 		if (r->ntc_temp != r->ntc_temp) { // NaNs are never equal to themselves
// 			counter++;
// 		} else {
// 			printf("ACD = %u, Temp = %f\n",ntc_adc, report->ntc_temp);
// 		}
// 	}
// 	printf("NaN = %d\n", counter);
// 	// Results: Most numbers come out as nan: 64510 / 65536
// }

