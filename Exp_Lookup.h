// Lookup Table for converting log detector to linear power responce.
//  Bruce Randall  Sept 24, 2019 change to 0 to 32767 data range.
// Table below from spreadsheet calcs.  32766 = Full Scale.
#define TableShift 7          // Shift right count for 255 full scale to PWM
#define TableLen 1025         // dummy added on end for interp process
const unsigned int lookup[TableLen] PROGMEM = {
// ,// AD8318 span of 508mv & 32766 FS I/O
279,//
280,//
281,//
283,//
284,//
285,//
287,//
288,//
289,//
291,//
292,//
293,//
295,//
296,//
298,//
299,//
300,//
302,//
303,//
305,//
306,//
307,//
309,//
310,//
312,//
313,//
315,//
316,//
318,//
319,//
321,//
322,//
324,//
325,//
327,//
328,//
330,//
331,//
333,//
334,//
336,//
337,//
339,//
341,//
342,//
344,//
345,//
347,//
349,//
350,//
352,//
354,//
355,//
357,//
359,//
360,//
362,//
364,//
365,//
367,//
369,//
370,//
372,//
374,//
376,//
377,//
379,//
381,//
383,//
384,//
386,//
388,//
390,//
392,//
394,//
395,//
397,//
399,//
401,//
403,//
405,//
407,//
408,//
410,//
412,//
414,//
416,//
418,//
420,//
422,//
424,//
426,//
428,//
430,//
432,//
434,//
436,//
438,//
440,//
442,//
444,//
446,//
448,//
450,//
453,//
455,//
457,//
459,//
461,//
463,//
465,//
468,//
470,//
472,//
474,//
476,//
479,//
481,//
483,//
485,//
488,//
490,//
492,//
494,//
497,//
499,//
501,//
504,//
506,//
508,//
511,//
513,//
516,//
518,//
520,//
523,//
525,//
528,//
530,//
533,//
535,//
538,//
540,//
543,//
545,//
548,//
550,//
553,//
556,//
558,//
561,//
563,//
566,//
569,//
571,//
574,//
577,//
579,//
582,//
585,//
588,//
590,//
593,//
596,//
599,//
601,//
604,//
607,//
610,//
613,//
616,//
618,//
621,//
624,//
627,//
630,//
633,//
636,//
639,//
642,//
645,//
648,//
651,//
654,//
657,//
660,//
663,//
666,//
669,//
673,//
676,//
679,//
682,//
685,//
688,//
692,//
695,//
698,//
701,//
705,//
708,//
711,//
715,//
718,//
721,//
725,//
728,//
731,//
735,//
738,//
742,//
745,//
749,//
752,//
756,//
759,//
763,//
766,//
770,//
773,//
777,//
781,//
784,//
788,//
792,//
795,//
799,//
803,//
807,//
810,//
814,//
818,//
822,//
826,//
829,//
833,//
837,//
841,//
845,//
849,//
853,//
857,//
861,//
865,//
869,//
873,//
877,//
881,//
885,//
889,//
894,//
898,//
902,//
906,//
910,//
915,//
919,//
923,//
928,//
932,//
936,//
941,//
945,//
949,//
954,//
958,//
963,//
967,//
972,//
976,//
981,//
985,//
990,//
995,//
999,//
1004,//
1009,//
1013,//
1018,//
1023,//
1028,//
1032,//
1037,//
1042,//
1047,//
1052,//
1057,//
1062,//
1067,//
1072,//
1077,//
1082,//
1087,//
1092,//
1097,//
1102,//
1107,//
1112,//
1118,//
1123,//
1128,//
1133,//
1139,//
1144,//
1149,//
1155,//
1160,//
1165,//
1171,//
1176,//
1182,//
1187,//
1193,//
1198,//
1204,//
1210,//
1215,//
1221,//
1227,//
1232,//
1238,//
1244,//
1250,//
1256,//
1262,//
1267,//
1273,//
1279,//
1285,//
1291,//
1297,//
1303,//
1309,//
1316,//
1322,//
1328,//
1334,//
1340,//
1347,//
1353,//
1359,//
1366,//
1372,//
1378,//
1385,//
1391,//
1398,//
1404,//
1411,//
1417,//
1424,//
1431,//
1437,//
1444,//
1451,//
1458,//
1464,//
1471,//
1478,//
1485,//
1492,//
1499,//
1506,//
1513,//
1520,//
1527,//
1534,//
1541,//
1549,//
1556,//
1563,//
1570,//
1578,//
1585,//
1592,//
1600,//
1607,//
1615,//
1622,//
1630,//
1638,//
1645,//
1653,//
1661,//
1668,//
1676,//
1684,//
1692,//
1700,//
1708,//
1716,//
1724,//
1732,//
1740,//
1748,//
1756,//
1764,//
1773,//
1781,//
1789,//
1798,//
1806,//
1814,//
1823,//
1831,//
1840,//
1849,//
1857,//
1866,//
1875,//
1883,//
1892,//
1901,//
1910,//
1919,//
1928,//
1937,//
1946,//
1955,//
1964,//
1973,//
1982,//
1992,//
2001,//
2010,//
2020,//
2029,//
2039,//
2048,//
2058,//
2067,//
2077,//
2087,//
2096,//
2106,//
2116,//
2126,//
2136,//
2146,//
2156,//
2166,//
2176,//
2186,//
2196,//
2207,//
2217,//
2227,//
2238,//
2248,//
2259,//
2269,//
2280,//
2290,//
2301,//
2312,//
2323,//
2334,//
2344,//
2355,//
2366,//
2377,//
2389,//
2400,//
2411,//
2422,//
2433,//
2445,//
2456,//
2468,//
2479,//
2491,//
2502,//
2514,//
2526,//
2538,//
2550,//
2561,//
2573,//
2585,//
2598,//
2610,//
2622,//
2634,//
2646,//
2659,//
2671,//
2684,//
2696,//
2709,//
2721,//
2734,//
2747,//
2760,//
2773,//
2786,//
2799,//
2812,//
2825,//
2838,//
2851,//
2865,//
2878,//
2891,//
2905,//
2918,//
2932,//
2946,//
2960,//
2973,//
2987,//
3001,//
3015,//
3029,//
3043,//
3058,//
3072,//
3086,//
3101,//
3115,//
3130,//
3144,//
3159,//
3174,//
3189,//
3203,//
3218,//
3233,//
3249,//
3264,//
3279,//
3294,//
3310,//
3325,//
3341,//
3356,//
3372,//
3388,//
3404,//
3419,//
3435,//
3451,//
3468,//
3484,//
3500,//
3516,//
3533,//
3549,//
3566,//
3583,//
3599,//
3616,//
3633,//
3650,//
3667,//
3684,//
3701,//
3719,//
3736,//
3753,//
3771,//
3789,//
3806,//
3824,//
3842,//
3860,//
3878,//
3896,//
3914,//
3932,//
3951,//
3969,//
3988,//
4006,//
4025,//
4044,//
4063,//
4082,//
4101,//
4120,//
4139,//
4159,//
4178,//
4198,//
4217,//
4237,//
4257,//
4276,//
4296,//
4317,//
4337,//
4357,//
4377,//
4398,//
4418,//
4439,//
4460,//
4480,//
4501,//
4522,//
4544,//
4565,//
4586,//
4608,//
4629,//
4651,//
4672,//
4694,//
4716,//
4738,//
4760,//
4782,//
4805,//
4827,//
4850,//
4872,//
4895,//
4918,//
4941,//
4964,//
4987,//
5011,//
5034,//
5058,//
5081,//
5105,//
5129,//
5153,//
5177,//
5201,//
5225,//
5250,//
5274,//
5299,//
5324,//
5348,//
5373,//
5398,//
5424,//
5449,//
5474,//
5500,//
5526,//
5552,//
5577,//
5603,//
5630,//
5656,//
5682,//
5709,//
5736,//
5762,//
5789,//
5816,//
5843,//
5871,//
5898,//
5926,//
5953,//
5981,//
6009,//
6037,//
6065,//
6094,//
6122,//
6151,//
6180,//
6208,//
6237,//
6267,//
6296,//
6325,//
6355,//
6384,//
6414,//
6444,//
6474,//
6505,//
6535,//
6565,//
6596,//
6627,//
6658,//
6689,//
6720,//
6752,//
6783,//
6815,//
6847,//
6879,//
6911,//
6943,//
6975,//
7008,//
7041,//
7074,//
7107,//
7140,//
7173,//
7207,//
7240,//
7274,//
7308,//
7342,//
7377,//
7411,//
7446,//
7480,//
7515,//
7550,//
7586,//
7621,//
7657,//
7692,//
7728,//
7765,//
7801,//
7837,//
7874,//
7911,//
7948,//
7985,//
8022,//
8059,//
8097,//
8135,//
8173,//
8211,//
8249,//
8288,//
8327,//
8366,//
8405,//
8444,//
8483,//
8523,//
8563,//
8603,//
8643,//
8683,//
8724,//
8765,//
8805,//
8847,//
8888,//
8929,//
8971,//
9013,//
9055,//
9097,//
9140,//
9183,//
9225,//
9269,//
9312,//
9355,//
9399,//
9443,//
9487,//
9531,//
9576,//
9621,//
9666,//
9711,//
9756,//
9802,//
9847,//
9893,//
9940,//
9986,//
10033,//
10079,//
10127,//
10174,//
10221,//
10269,//
10317,//
10365,//
10414,//
10462,//
10511,//
10560,//
10610,//
10659,//
10709,//
10759,//
10809,//
10860,//
10910,//
10961,//
11013,//
11064,//
11116,//
11168,//
11220,//
11272,//
11325,//
11378,//
11431,//
11484,//
11538,//
11592,//
11646,//
11700,//
11755,//
11810,//
11865,//
11920,//
11976,//
12032,//
12088,//
12145,//
12201,//
12258,//
12316,//
12373,//
12431,//
12489,//
12547,//
12606,//
12665,//
12724,//
12783,//
12843,//
12903,//
12963,//
13024,//
13085,//
13146,//
13207,//
13269,//
13331,//
13393,//
13456,//
13518,//
13582,//
13645,//
13709,//
13773,//
13837,//
13902,//
13967,//
14032,//
14097,//
14163,//
14229,//
14296,//
14363,//
14430,//
14497,//
14565,//
14633,//
14701,//
14770,//
14839,//
14908,//
14978,//
15048,//
15118,//
15189,//
15260,//
15331,//
15402,//
15474,//
15547,//
15619,//
15692,//
15766,//
15839,//
15913,//
15987,//
16062,//
16137,//
16212,//
16288,//
16364,//
16441,//
16518,//
16595,//
16672,//
16750,//
16828,//
16907,//
16986,//
17065,//
17145,//
17225,//
17305,//
17386,//
17467,//
17549,//
17631,//
17713,//
17796,//
17879,//
17963,//
18047,//
18131,//
18215,//
18301,//
18386,//
18472,//
18558,//
18645,//
18732,//
18819,//
18907,//
18996,//
19084,//
19173,//
19263,//
19353,//
19443,//
19534,//
19625,//
19717,//
19809,//
19902,//
19995,//
20088,//
20182,//
20276,//
20371,//
20466,//
20562,//
20658,//
20754,//
20851,//
20948,//
21046,//
21145,//
21243,//
21342,//
21442,//
21542,//
21643,//
21744,//
21846,//
21948,//
22050,//
22153,//
22257,//
22360,//
22465,//
22570,//
22675,//
22781,//
22888,//
22994,//
23102,//
23210,//
23318,//
23427,//
23536,//
23646,//
23757,//
23868,//
23979,//
24091,//
24204,//
24317,//
24430,//
24545,//
24659,//
24774,//
24890,//
25006,//
25123,//
25240,//
25358,//
25477,//
25596,//
25715,//
25835,//
25956,//
26077,//
26199,//
26321,//
26444,//
26568,//
26692,//
26817,//
26942,//
27068,//
27194,//
27321,//
27449,//
27577,//
27706,//
27835,//
27965,//
28096,//
28227,//
28359,//
28491,//
28624,//
28758,//
28892,//
29027,//
29163,//
29299,//
29436,//
29573,//
29711,//
29850,//
29990,//
30130,//
30270,//
30412,//
30554,//
30697,//
30840,//
30984,//
31129,//
31274,//
31420,//
31567,//
31714,//
31862,//
32011,//
32161,//
32311,//
32462,//
32613,//
32766,//
32767 // dummy on end 
};

/* old 14 bit data in comment below
// ,// AD8318 span of 508mv & 16383 FS I/O
139,//
140,//
141,//
141,//
142,//
143,//
143,//
144,//
145,//
145,//
146,//
147,//
147,//
148,//
149,//
149,//
150,//
151,//
152,//
152,//
153,//
154,//
154,//
155,//
156,//
157,//
157,//
158,//
159,//
160,//
160,//
161,//
162,//
163,//
163,//
164,//
165,//
166,//
166,//
167,//
168,//
169,//
169,//
170,//
171,//
172,//
173,//
173,//
174,//
175,//
176,//
177,//
178,//
178,//
179,//
180,//
181,//
182,//
183,//
183,//
184,//
185,//
186,//
187,//
188,//
189,//
190,//
190,//
191,//
192,//
193,//
194,//
195,//
196,//
197,//
198,//
199,//
200,//
200,//
201,//
202,//
203,//
204,//
205,//
206,//
207,//
208,//
209,//
210,//
211,//
212,//
213,//
214,//
215,//
216,//
217,//
218,//
219,//
220,//
221,//
222,//
223,//
224,//
225,//
226,//
227,//
228,//
229,//
231,//
232,//
233,//
234,//
235,//
236,//
237,//
238,//
239,//
240,//
242,//
243,//
244,//
245,//
246,//
247,//
248,//
250,//
251,//
252,//
253,//
254,//
255,//
257,//
258,//
259,//
260,//
261,//
263,//
264,//
265,//
266,//
268,//
269,//
270,//
271,//
273,//
274,//
275,//
276,//
278,//
279,//
280,//
282,//
283,//
284,//
286,//
287,//
288,//
290,//
291,//
292,//
294,//
295,//
296,//
298,//
299,//
301,//
302,//
303,//
305,//
306,//
308,//
309,//
311,//
312,//
314,//
315,//
316,//
318,//
319,//
321,//
322,//
324,//
325,//
327,//
328,//
330,//
332,//
333,//
335,//
336,//
338,//
339,//
341,//
343,//
344,//
346,//
347,//
349,//
351,//
352,//
354,//
356,//
357,//
359,//
361,//
362,//
364,//
366,//
367,//
369,//
371,//
373,//
374,//
376,//
378,//
380,//
381,//
383,//
385,//
387,//
388,//
390,//
392,//
394,//
396,//
398,//
399,//
401,//
403,//
405,//
407,//
409,//
411,//
413,//
415,//
417,//
419,//
420,//
422,//
424,//
426,//
428,//
430,//
432,//
434,//
436,//
438,//
441,//
443,//
445,//
447,//
449,//
451,//
453,//
455,//
457,//
459,//
462,//
464,//
466,//
468,//
470,//
472,//
475,//
477,//
479,//
481,//
484,//
486,//
488,//
490,//
493,//
495,//
497,//
500,//
502,//
504,//
507,//
509,//
511,//
514,//
516,//
519,//
521,//
523,//
526,//
528,//
531,//
533,//
536,//
538,//
541,//
543,//
546,//
548,//
551,//
554,//
556,//
559,//
561,//
564,//
567,//
569,//
572,//
575,//
577,//
580,//
583,//
585,//
588,//
591,//
594,//
596,//
599,//
602,//
605,//
608,//
610,//
613,//
616,//
619,//
622,//
625,//
628,//
631,//
634,//
637,//
640,//
643,//
646,//
649,//
652,//
655,//
658,//
661,//
664,//
667,//
670,//
673,//
676,//
679,//
683,//
686,//
689,//
692,//
695,//
699,//
702,//
705,//
709,//
712,//
715,//
719,//
722,//
725,//
729,//
732,//
735,//
739,//
742,//
746,//
749,//
753,//
756,//
760,//
763,//
767,//
771,//
774,//
778,//
781,//
785,//
789,//
792,//
796,//
800,//
804,//
807,//
811,//
815,//
819,//
823,//
826,//
830,//
834,//
838,//
842,//
846,//
850,//
854,//
858,//
862,//
866,//
870,//
874,//
878,//
882,//
886,//
890,//
894,//
899,//
903,//
907,//
911,//
916,//
920,//
924,//
928,//
933,//
937,//
942,//
946,//
950,//
955,//
959,//
964,//
968,//
973,//
977,//
982,//
986,//
991,//
996,//
1000,//
1005,//
1010,//
1014,//
1019,//
1024,//
1029,//
1033,//
1038,//
1043,//
1048,//
1053,//
1058,//
1063,//
1068,//
1073,//
1078,//
1083,//
1088,//
1093,//
1098,//
1103,//
1108,//
1113,//
1119,//
1124,//
1129,//
1134,//
1140,//
1145,//
1150,//
1156,//
1161,//
1167,//
1172,//
1178,//
1183,//
1189,//
1194,//
1200,//
1205,//
1211,//
1217,//
1222,//
1228,//
1234,//
1239,//
1245,//
1251,//
1257,//
1263,//
1269,//
1275,//
1281,//
1287,//
1293,//
1299,//
1305,//
1311,//
1317,//
1323,//
1329,//
1335,//
1342,//
1348,//
1354,//
1361,//
1367,//
1373,//
1380,//
1386,//
1393,//
1399,//
1406,//
1412,//
1419,//
1425,//
1432,//
1439,//
1445,//
1452,//
1459,//
1466,//
1473,//
1480,//
1486,//
1493,//
1500,//
1507,//
1514,//
1521,//
1529,//
1536,//
1543,//
1550,//
1557,//
1565,//
1572,//
1579,//
1587,//
1594,//
1602,//
1609,//
1617,//
1624,//
1632,//
1639,//
1647,//
1655,//
1662,//
1670,//
1678,//
1686,//
1694,//
1702,//
1709,//
1717,//
1725,//
1734,//
1742,//
1750,//
1758,//
1766,//
1774,//
1783,//
1791,//
1799,//
1808,//
1816,//
1825,//
1833,//
1842,//
1850,//
1859,//
1868,//
1876,//
1885,//
1894,//
1903,//
1912,//
1921,//
1930,//
1939,//
1948,//
1957,//
1966,//
1975,//
1984,//
1994,//
2003,//
2012,//
2022,//
2031,//
2041,//
2050,//
2060,//
2069,//
2079,//
2089,//
2098,//
2108,//
2118,//
2128,//
2138,//
2148,//
2158,//
2168,//
2178,//
2188,//
2199,//
2209,//
2219,//
2230,//
2240,//
2250,//
2261,//
2271,//
2282,//
2293,//
2303,//
2314,//
2325,//
2336,//
2347,//
2358,//
2369,//
2380,//
2391,//
2402,//
2413,//
2425,//
2436,//
2447,//
2459,//
2470,//
2482,//
2493,//
2505,//
2517,//
2528,//
2540,//
2552,//
2564,//
2576,//
2588,//
2600,//
2612,//
2624,//
2637,//
2649,//
2661,//
2674,//
2686,//
2699,//
2711,//
2724,//
2737,//
2750,//
2762,//
2775,//
2788,//
2801,//
2814,//
2828,//
2841,//
2854,//
2867,//
2881,//
2894,//
2908,//
2921,//
2935,//
2949,//
2962,//
2976,//
2990,//
3004,//
3018,//
3032,//
3046,//
3061,//
3075,//
3089,//
3104,//
3118,//
3133,//
3147,//
3162,//
3177,//
3192,//
3207,//
3222,//
3237,//
3252,//
3267,//
3282,//
3298,//
3313,//
3328,//
3344,//
3360,//
3375,//
3391,//
3407,//
3423,//
3439,//
3455,//
3471,//
3487,//
3503,//
3520,//
3536,//
3553,//
3569,//
3586,//
3603,//
3620,//
3637,//
3654,//
3671,//
3688,//
3705,//
3722,//
3740,//
3757,//
3775,//
3792,//
3810,//
3828,//
3846,//
3864,//
3882,//
3900,//
3918,//
3936,//
3955,//
3973,//
3992,//
4010,//
4029,//
4048,//
4067,//
4086,//
4105,//
4124,//
4143,//
4163,//
4182,//
4202,//
4221,//
4241,//
4261,//
4281,//
4301,//
4321,//
4341,//
4361,//
4382,//
4402,//
4423,//
4443,//
4464,//
4485,//
4506,//
4527,//
4548,//
4569,//
4591,//
4612,//
4634,//
4655,//
4677,//
4699,//
4721,//
4743,//
4765,//
4787,//
4810,//
4832,//
4855,//
4877,//
4900,//
4923,//
4946,//
4969,//
4992,//
5016,//
5039,//
5063,//
5086,//
5110,//
5134,//
5158,//
5182,//
5206,//
5230,//
5255,//
5279,//
5304,//
5329,//
5354,//
5379,//
5404,//
5429,//
5454,//
5480,//
5505,//
5531,//
5557,//
5583,//
5609,//
5635,//
5662,//
5688,//
5715,//
5741,//
5768,//
5795,//
5822,//
5849,//
5877,//
5904,//
5932,//
5959,//
5987,//
6015,//
6043,//
6071,//
6100,//
6128,//
6157,//
6186,//
6215,//
6244,//
6273,//
6302,//
6331,//
6361,//
6391,//
6421,//
6451,//
6481,//
6511,//
6541,//
6572,//
6603,//
6633,//
6664,//
6696,//
6727,//
6758,//
6790,//
6822,//
6853,//
6885,//
6918,//
6950,//
6982,//
7015,//
7048,//
7081,//
7114,//
7147,//
7180,//
7214,//
7248,//
7281,//
7315,//
7350,//
7384,//
7418,//
7453,//
7488,//
7523,//
7558,//
7593,//
7629,//
7664,//
7700,//
7736,//
7772,//
7809,//
7845,//
7882,//
7918,//
7955,//
7993,//
8030,//
8067,//
8105,//
8143,//
8181,//
8219,//
8258,//
8296,//
8335,//
8374,//
8413,//
8452,//
8492,//
8531,//
8571,//
8611,//
8651,//
8692,//
8732,//
8773,//
8814,//
8855,//
8897,//
8938,//
8980,//
9022,//
9064,//
9106,//
9149,//
9192,//
9235,//
9278,//
9321,//
9365,//
9408,//
9452,//
9496,//
9541,//
9585,//
9630,//
9675,//
9720,//
9766,//
9811,//
9857,//
9903,//
9949,//
9996,//
10043,//
10089,//
10137,//
10184,//
10232,//
10279,//
10327,//
10376,//
10424,//
10473,//
10522,//
10571,//
10620,//
10670,//
10720,//
10770,//
10820,//
10870,//
10921,//
10972,//
11023,//
11075,//
11127,//
11179,//
11231,//
11283,//
11336,//
11389,//
11442,//
11496,//
11549,//
11603,//
11657,//
11712,//
11767,//
11822,//
11877,//
11932,//
11988,//
12044,//
12100,//
12157,//
12213,//
12270,//
12328,//
12385,//
12443,//
12501,//
12560,//
12618,//
12677,//
12737,//
12796,//
12856,//
12916,//
12976,//
13037,//
13098,//
13159,//
13220,//
13282,//
13344,//
13406,//
13469,//
13532,//
13595,//
13659,//
13722,//
13786,//
13851,//
13916,//
13981,//
14046,//
14111,//
14177,//
14244,//
14310,//
14377,//
14444,//
14512,//
14579,//
14647,//
14716,//
14785,//
14854,//
14923,//
14993,//
15063,//
15133,//
15204,//
15275,//
15346,//
15418,//
15490,//
15562,//
15635,//
15708,//
15781,//
15855,//
15929,//
16003,//
16078,//
16153,//
16229,//
16304,//
16381,//
16383 // dummy on end 
};
*/ 
//end of old 14 bit data 
