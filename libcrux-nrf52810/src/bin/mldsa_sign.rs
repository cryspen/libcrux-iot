#![no_main]
#![no_std]
#![cfg(feature = "mldsa87")]

use libcrux_nrf52810 as board; // global logger + panicking-behavior + memory layout

use libcrux_ml_dsa::ml_dsa_87 as mldsa;

static SK: [u8; 4896] = [
    158, 41, 234, 146, 185, 41, 27, 225, 46, 178, 46, 248, 151, 40, 73, 59, 147, 27, 116, 81, 248,
    8, 158, 148, 78, 73, 68, 45, 224, 13, 255, 41, 95, 188, 191, 236, 222, 219, 178, 26, 88, 255,
    5, 115, 10, 204, 221, 181, 37, 54, 137, 40, 175, 208, 55, 241, 171, 20, 118, 249, 13, 181, 246,
    108, 74, 3, 40, 45, 47, 127, 100, 148, 161, 189, 66, 110, 70, 113, 83, 148, 102, 208, 241, 33,
    165, 137, 177, 139, 97, 53, 42, 162, 106, 146, 182, 249, 94, 176, 19, 169, 10, 94, 231, 91,
    171, 19, 1, 165, 28, 249, 215, 255, 111, 152, 135, 125, 191, 1, 82, 0, 15, 180, 221, 233, 77,
    113, 201, 85, 64, 130, 77, 10, 35, 0, 34, 193, 96, 163, 16, 49, 0, 64, 34, 35, 3, 100, 128, 68,
    140, 72, 132, 145, 3, 200, 101, 35, 56, 0, 225, 2, 64, 24, 69, 32, 36, 192, 137, 84, 16, 74,
    68, 16, 4, 12, 16, 2, 11, 25, 110, 200, 198, 4, 4, 129, 16, 64, 160, 4, 92, 2, 46, 33, 195,
    101, 131, 0, 16, 162, 70, 78, 137, 40, 129, 88, 34, 68, 76, 20, 8, 3, 56, 77, 1, 19, 110, 28,
    152, 33, 201, 24, 78, 220, 166, 101, 100, 152, 144, 68, 184, 44, 228, 184, 73, 11, 65, 37, 92,
    54, 34, 12, 8, 34, 152, 152, 81, 196, 8, 2, 131, 196, 32, 3, 7, 77, 211, 132, 97, 209, 192,
    100, 16, 69, 137, 11, 161, 0, 155, 22, 14, 92, 64, 80, 218, 70, 140, 8, 73, 76, 212, 40, 33,
    64, 36, 113, 4, 2, 145, 88, 200, 129, 218, 160, 12, 12, 69, 138, 99, 128, 140, 98, 2, 6, 204,
    144, 145, 195, 56, 66, 156, 48, 33, 84, 200, 32, 100, 72, 96, 210, 54, 6, 99, 6, 66, 12, 72,
    14, 32, 193, 144, 200, 56, 130, 17, 133, 36, 192, 54, 146, 74, 132, 44, 164, 72, 0, 228, 50,
    17, 210, 32, 38, 211, 176, 80, 9, 25, 18, 0, 55, 14, 12, 165, 33, 34, 2, 110, 92, 152, 4, 208,
    176, 1, 8, 34, 10, 130, 36, 50, 88, 8, 13, 220, 54, 137, 25, 198, 112, 220, 50, 81, 9, 192,
    129, 12, 67, 12, 11, 39, 112, 130, 38, 96, 193, 16, 72, 227, 182, 76, 148, 4, 65, 11, 24, 69,
    216, 66, 144, 152, 48, 110, 138, 0, 144, 131, 22, 10, 3, 137, 17, 163, 66, 34, 144, 184, 1, 26,
    24, 140, 35, 54, 133, 0, 65, 66, 130, 18, 66, 220, 176, 4, 16, 54, 114, 82, 24, 8, 144, 18, 44,
    24, 57, 9, 32, 7, 129, 0, 177, 17, 27, 36, 5, 19, 24, 69, 137, 136, 108, 34, 69, 77, 147, 130,
    80, 68, 70, 142, 130, 128, 12, 1, 167, 113, 84, 128, 100, 4, 68, 138, 226, 198, 96, 200, 68,
    98, 226, 72, 17, 162, 16, 72, 152, 176, 65, 67, 34, 10, 65, 2, 34, 28, 16, 70, 204, 70, 41,
    162, 20, 70, 225, 134, 104, 2, 1, 106, 210, 128, 137, 68, 194, 44, 1, 54, 145, 12, 36, 69, 17,
    54, 105, 35, 166, 77, 146, 134, 129, 132, 18, 140, 202, 70, 97, 17, 166, 96, 25, 148, 105, 216,
    192, 109, 100, 40, 66, 100, 160, 141, 82, 16, 14, 17, 49, 78, 212, 70, 73, 139, 184, 104, 25,
    179, 72, 208, 166, 5, 32, 48, 102, 33, 36, 9, 0, 18, 0, 18, 64, 2, 36, 73, 133, 10, 73, 141,
    81, 4, 100, 139, 36, 144, 82, 32, 49, 8, 135, 140, 208, 168, 41, 195, 130, 113, 67, 70, 80,
    209, 38, 44, 152, 48, 145, 138, 2, 64, 16, 161, 4, 19, 51, 17, 128, 0, 133, 193, 68, 50, 75,
    68, 42, 17, 69, 130, 27, 65, 96, 216, 176, 80, 10, 181, 1, 8, 36, 50, 83, 134, 33, 219, 52, 18,
    76, 22, 140, 154, 146, 13, 84, 164, 113, 212, 146, 69, 4, 145, 12, 92, 130, 12, 219, 20, 50,
    20, 128, 49, 12, 5, 112, 11, 70, 49, 35, 19, 109, 217, 146, 0, 65, 36, 98, 28, 161, 112, 9, 65,
    76, 24, 48, 41, 219, 50, 14, 24, 160, 96, 99, 180, 141, 137, 200, 65, 218, 54, 70, 36, 17, 14,
    91, 50, 108, 148, 0, 44, 11, 32, 141, 16, 145, 12, 8, 166, 17, 4, 72, 34, 26, 57, 96, 225, 32,
    138, 137, 152, 40, 163, 134, 0, 152, 38, 37, 132, 38, 140, 27, 66, 49, 4, 179, 9, 195, 184, 76,
    216, 34, 37, 90, 196, 145, 210, 24, 66, 34, 54, 78, 91, 6, 4, 81, 132, 80, 211, 20, 13, 33, 68,
    138, 32, 18, 18, 27, 32, 105, 3, 147, 8, 209, 184, 128, 27, 64, 102, 97, 72, 138, 32, 145, 104,
    128, 20, 46, 154, 198, 73, 140, 32, 141, 11, 67, 97, 91, 0, 113, 4, 7, 33, 130, 130, 65, 210,
    180, 104, 64, 18, 50, 227, 0, 141, 66, 64, 12, 9, 8, 16, 147, 194, 64, 152, 148, 12, 100, 52,
    114, 202, 166, 145, 194, 24, 110, 128, 8, 13, 35, 9, 105, 36, 182, 104, 80, 152, 45, 200, 38,
    46, 25, 32, 108, 91, 22, 130, 140, 130, 16, 4, 48, 42, 162, 70, 77, 26, 130, 100, 136, 150,
    144, 36, 168, 4, 19, 2, 64, 99, 64, 66, 225, 136, 100, 162, 16, 6, 100, 72, 45, 131, 66, 1, 17,
    38, 40, 73, 184, 137, 17, 65, 106, 163, 0, 65, 1, 21, 44, 34, 166, 45, 220, 134, 65, 201, 50,
    6, 156, 40, 77, 32, 53, 80, 17, 20, 138, 84, 22, 5, 81, 4, 110, 3, 35, 128, 202, 192, 76, 96,
    2, 50, 72, 68, 41, 19, 164, 12, 195, 64, 102, 155, 38, 76, 209, 6, 77, 91, 8, 40, 36, 200, 104,
    10, 144, 73, 194, 54, 80, 72, 16, 81, 75, 70, 65, 204, 22, 74, 218, 68, 14, 98, 64, 128, 131,
    176, 68, 98, 136, 144, 148, 0, 48, 18, 53, 69, 24, 162, 136, 208, 148, 33, 228, 132, 48, 19,
    193, 0, 82, 64, 101, 89, 194, 144, 0, 54, 77, 32, 152, 72, 204, 194, 13, 217, 182, 140, 25, 0,
    17, 16, 8, 4, 66, 52, 72, 32, 183, 8, 33, 33, 70, 161, 4, 41, 67, 64, 80, 67, 152, 9, 8, 182,
    144, 9, 128, 48, 194, 200, 9, 36, 3, 108, 226, 164, 72, 66, 40, 48, 227, 160, 44, 4, 166, 48,
    216, 184, 100, 9, 38, 37, 20, 136, 12, 19, 165, 4, 204, 32, 45, 35, 6, 70, 16, 38, 10, 19, 167,
    41, 88, 66, 114, 161, 162, 97, 195, 160, 137, 88, 38, 76, 208, 40, 49, 27, 40, 32, 220, 18, 5,
    88, 134, 145, 218, 0, 32, 8, 39, 98, 227, 146, 45, 4, 193, 17, 211, 148, 104, 91, 52, 46, 3,
    32, 96, 80, 164, 8, 161, 0, 16, 224, 200, 137, 204, 22, 106, 148, 52, 5, 137, 32, 113, 26, 137,
    16, 64, 70, 96, 129, 34, 110, 211, 178, 69, 82, 50, 112, 20, 41, 106, 16, 69, 64, 76, 22, 9,
    218, 4, 50, 35, 129, 76, 17, 66, 37, 153, 198, 49, 25, 197, 101, 73, 0, 102, 35, 37, 138, 25,
    70, 41, 148, 128, 44, 162, 130, 69, 99, 182, 129, 11, 6, 12, 1, 185, 4, 194, 130, 109, 204,
    168, 140, 225, 168, 16, 20, 167, 128, 130, 182, 9, 28, 68, 2, 100, 160, 81, 3, 196, 9, 28, 201,
    12, 34, 168, 101, 212, 194, 72, 25, 4, 49, 18, 164, 96, 163, 64, 112, 67, 36, 136, 66, 70, 108,
    19, 149, 113, 131, 22, 0, 24, 199, 137, 33, 169, 141, 220, 164, 113, 17, 144, 112, 156, 8, 0,
    202, 54, 128, 91, 34, 48, 10, 69, 146, 9, 54, 133, 19, 184, 16, 161, 34, 44, 148, 64, 12, 131,
    66, 81, 132, 2, 109, 91, 68, 109, 25, 133, 68, 18, 185, 13, 130, 48, 34, 9, 130, 41, 64, 152,
    8, 144, 68, 49, 64, 66, 8, 160, 180, 137, 25, 134, 45, 12, 70, 97, 130, 0, 46, 8, 180, 36, 24,
    197, 77, 80, 162, 0, 8, 130, 105, 147, 50, 40, 138, 48, 13, 200, 134, 49, 129, 196, 44, 96, 68,
    66, 28, 57, 40, 128, 184, 4, 19, 148, 64, 16, 34, 37, 162, 32, 134, 1, 20, 113, 17, 168, 40, 3,
    71, 145, 216, 192, 141, 88, 54, 5, 136, 148, 129, 16, 9, 4, 96, 146, 104, 139, 36, 34, 20, 72,
    65, 25, 153, 36, 164, 192, 137, 227, 194, 16, 2, 37, 34, 3, 160, 105, 227, 136, 40, 200, 6, 6,
    90, 72, 36, 11, 37, 142, 2, 16, 96, 28, 38, 114, 200, 38, 109, 72, 166, 5, 224, 6, 6, 12, 0,
    42, 0, 69, 42, 17, 167, 40, 217, 176, 8, 35, 9, 138, 80, 20, 137, 91, 134, 101, 64, 56, 137,
    16, 178, 33, 99, 36, 0, 0, 8, 9, 228, 6, 9, 34, 144, 97, 137, 144, 137, 132, 6, 16, 83, 52,
    110, 217, 144, 80, 21, 111, 144, 18, 80, 120, 227, 52, 84, 168, 205, 226, 7, 139, 105, 134, 80,
    92, 200, 160, 74, 49, 29, 176, 139, 107, 159, 26, 249, 8, 182, 6, 214, 157, 136, 116, 24, 178,
    28, 56, 90, 127, 202, 231, 235, 127, 233, 154, 209, 201, 152, 203, 186, 27, 251, 146, 201, 135,
    227, 58, 255, 37, 206, 74, 142, 142, 181, 68, 32, 36, 229, 73, 219, 223, 251, 171, 15, 139, 13,
    105, 184, 53, 53, 24, 255, 41, 93, 173, 26, 147, 41, 179, 87, 9, 172, 150, 196, 121, 66, 68,
    76, 61, 225, 57, 35, 66, 11, 84, 181, 233, 197, 232, 119, 55, 117, 34, 107, 160, 79, 11, 11,
    39, 191, 175, 50, 86, 253, 173, 2, 160, 36, 68, 237, 184, 236, 162, 101, 39, 75, 59, 145, 164,
    192, 202, 131, 235, 252, 188, 24, 189, 42, 159, 104, 206, 187, 40, 67, 99, 108, 55, 158, 141,
    13, 110, 153, 61, 185, 70, 49, 147, 25, 199, 27, 251, 132, 169, 102, 68, 170, 146, 88, 20, 229,
    10, 140, 203, 17, 236, 244, 130, 78, 4, 86, 227, 168, 36, 220, 167, 237, 137, 133, 212, 184,
    72, 186, 241, 224, 119, 123, 110, 188, 184, 17, 75, 250, 212, 228, 76, 44, 206, 144, 87, 68,
    97, 31, 220, 87, 26, 130, 34, 119, 41, 55, 88, 19, 65, 42, 145, 155, 124, 123, 8, 142, 64, 243,
    66, 152, 74, 116, 30, 108, 99, 141, 13, 238, 224, 134, 2, 103, 89, 7, 69, 186, 174, 100, 17,
    123, 113, 123, 94, 210, 112, 122, 51, 204, 229, 90, 205, 54, 151, 26, 203, 140, 81, 241, 37,
    14, 73, 75, 207, 91, 166, 28, 110, 33, 110, 70, 72, 124, 94, 36, 81, 247, 46, 65, 146, 59, 158,
    5, 164, 249, 227, 151, 35, 81, 43, 189, 36, 210, 142, 103, 120, 164, 129, 218, 43, 172, 85, 36,
    13, 79, 195, 52, 16, 133, 54, 49, 235, 156, 83, 17, 195, 209, 28, 62, 114, 176, 112, 200, 25,
    118, 184, 125, 9, 240, 19, 1, 193, 65, 247, 199, 201, 27, 208, 73, 219, 248, 28, 26, 78, 105,
    179, 155, 236, 116, 22, 137, 240, 96, 96, 126, 220, 169, 118, 228, 178, 228, 71, 41, 40, 71,
    187, 97, 33, 63, 226, 85, 238, 245, 17, 254, 189, 241, 183, 176, 36, 40, 98, 210, 243, 254, 35,
    241, 162, 114, 242, 185, 160, 155, 89, 78, 110, 188, 144, 149, 54, 191, 15, 118, 174, 134, 84,
    190, 13, 110, 28, 188, 106, 151, 163, 251, 75, 116, 141, 172, 39, 5, 242, 38, 133, 51, 215,
    170, 86, 4, 21, 168, 244, 70, 239, 178, 111, 39, 70, 200, 35, 107, 96, 131, 205, 158, 135, 83,
    218, 62, 212, 143, 17, 108, 185, 182, 125, 236, 120, 180, 67, 242, 96, 72, 244, 225, 154, 162,
    95, 85, 215, 242, 168, 160, 137, 50, 49, 177, 58, 154, 37, 120, 182, 222, 60, 244, 128, 124,
    101, 128, 188, 44, 7, 98, 100, 172, 205, 211, 34, 247, 154, 128, 244, 4, 29, 73, 145, 153, 100,
    253, 146, 203, 81, 147, 167, 56, 60, 33, 244, 166, 11, 52, 193, 59, 120, 190, 105, 86, 12, 249,
    119, 51, 251, 125, 63, 156, 196, 211, 86, 212, 140, 53, 37, 207, 52, 135, 209, 99, 234, 8, 189,
    123, 244, 212, 237, 46, 168, 230, 43, 110, 72, 193, 248, 22, 189, 137, 35, 17, 121, 194, 38,
    98, 247, 240, 248, 114, 104, 22, 4, 121, 96, 107, 128, 114, 48, 86, 162, 8, 17, 146, 17, 86,
    217, 178, 178, 117, 236, 142, 209, 14, 227, 242, 142, 37, 248, 175, 75, 186, 47, 128, 145, 183,
    66, 72, 126, 44, 254, 34, 104, 92, 76, 231, 21, 58, 28, 128, 230, 4, 165, 179, 195, 239, 231,
    232, 246, 54, 88, 71, 252, 150, 125, 50, 179, 154, 39, 194, 144, 208, 200, 167, 78, 168, 186,
    252, 180, 250, 51, 69, 222, 242, 245, 203, 116, 140, 7, 27, 157, 176, 67, 248, 41, 155, 222,
    88, 246, 111, 15, 202, 141, 150, 127, 219, 40, 128, 180, 134, 250, 32, 81, 156, 22, 62, 29,
    244, 221, 30, 120, 101, 87, 62, 224, 9, 192, 96, 35, 146, 30, 206, 24, 202, 205, 163, 243, 210,
    94, 87, 0, 209, 229, 94, 83, 20, 234, 205, 36, 241, 204, 74, 177, 117, 102, 8, 114, 95, 62,
    127, 144, 79, 249, 89, 246, 84, 158, 172, 195, 206, 187, 191, 146, 93, 147, 146, 0, 74, 73,
    196, 140, 219, 13, 132, 186, 123, 208, 163, 160, 140, 240, 34, 212, 3, 115, 184, 58, 32, 84,
    58, 249, 208, 224, 4, 138, 223, 34, 209, 170, 51, 1, 108, 148, 39, 32, 114, 179, 153, 85, 108,
    179, 207, 78, 255, 52, 232, 143, 111, 190, 59, 189, 201, 181, 178, 192, 29, 38, 170, 225, 72,
    208, 97, 92, 56, 136, 212, 145, 138, 88, 226, 63, 164, 104, 149, 245, 75, 26, 138, 156, 138,
    58, 32, 54, 85, 234, 167, 159, 80, 229, 81, 216, 220, 167, 205, 62, 151, 211, 126, 4, 38, 175,
    9, 80, 36, 248, 19, 80, 110, 192, 117, 29, 202, 169, 52, 111, 245, 144, 139, 191, 26, 23, 31,
    113, 151, 172, 156, 17, 115, 196, 247, 134, 254, 51, 117, 123, 26, 242, 27, 126, 71, 139, 57,
    188, 228, 252, 111, 141, 20, 54, 19, 164, 141, 47, 182, 242, 244, 220, 111, 230, 226, 229, 18,
    253, 17, 91, 186, 162, 85, 178, 37, 237, 163, 179, 29, 68, 223, 247, 195, 115, 133, 122, 172,
    112, 95, 91, 149, 213, 60, 239, 91, 111, 168, 30, 109, 112, 54, 50, 12, 74, 187, 148, 102, 40,
    232, 160, 71, 211, 156, 211, 215, 154, 13, 145, 65, 227, 24, 19, 133, 195, 96, 1, 230, 147, 75,
    205, 139, 12, 97, 82, 58, 113, 117, 204, 104, 251, 197, 76, 113, 63, 143, 218, 228, 25, 184,
    238, 180, 62, 174, 73, 176, 58, 205, 228, 125, 17, 102, 181, 194, 63, 152, 159, 141, 122, 88,
    68, 27, 231, 253, 38, 17, 238, 127, 64, 148, 243, 120, 190, 252, 74, 139, 87, 19, 45, 97, 149,
    133, 182, 147, 126, 125, 209, 239, 219, 166, 56, 250, 10, 204, 188, 64, 52, 133, 90, 41, 33,
    176, 164, 111, 244, 234, 55, 200, 243, 222, 197, 235, 149, 254, 242, 130, 11, 9, 20, 158, 12,
    33, 107, 169, 120, 222, 59, 136, 213, 66, 35, 122, 137, 32, 124, 181, 247, 158, 235, 22, 45,
    25, 128, 189, 1, 199, 67, 33, 136, 243, 229, 48, 168, 223, 159, 103, 160, 34, 196, 76, 199,
    176, 230, 162, 35, 202, 11, 211, 33, 68, 254, 95, 66, 244, 48, 102, 235, 136, 135, 23, 251, 94,
    49, 201, 90, 73, 110, 27, 55, 64, 164, 51, 251, 162, 179, 180, 114, 178, 13, 173, 1, 104, 94,
    85, 11, 82, 216, 85, 146, 21, 71, 103, 148, 203, 22, 153, 217, 105, 152, 238, 208, 192, 241,
    121, 241, 142, 165, 53, 200, 82, 181, 195, 185, 246, 64, 221, 73, 29, 36, 9, 151, 236, 53, 187,
    68, 50, 43, 16, 225, 103, 133, 242, 211, 70, 130, 224, 119, 43, 31, 103, 190, 153, 48, 35, 113,
    46, 67, 65, 61, 145, 207, 161, 104, 30, 221, 51, 39, 174, 35, 136, 238, 8, 119, 6, 25, 24, 156,
    89, 20, 197, 155, 22, 139, 92, 145, 112, 221, 54, 110, 221, 190, 30, 185, 94, 2, 245, 104, 122,
    254, 34, 141, 230, 179, 34, 7, 99, 170, 251, 25, 10, 53, 160, 120, 20, 226, 13, 62, 109, 125,
    29, 243, 232, 231, 176, 242, 176, 223, 29, 85, 48, 214, 189, 104, 153, 253, 134, 95, 253, 141,
    51, 70, 165, 206, 86, 189, 165, 28, 93, 85, 113, 20, 144, 179, 9, 127, 226, 153, 31, 155, 177,
    157, 218, 66, 53, 124, 183, 250, 12, 52, 188, 225, 112, 193, 47, 217, 92, 201, 216, 71, 143,
    32, 236, 254, 31, 87, 120, 198, 226, 115, 86, 188, 175, 103, 169, 106, 127, 133, 42, 234, 173,
    182, 235, 234, 171, 246, 138, 76, 105, 51, 108, 60, 15, 149, 71, 103, 43, 233, 50, 247, 141,
    222, 247, 141, 136, 168, 26, 75, 139, 16, 55, 159, 80, 144, 244, 70, 33, 204, 205, 216, 207,
    94, 96, 255, 148, 83, 191, 178, 108, 82, 220, 117, 209, 205, 236, 160, 210, 50, 109, 85, 30,
    46, 9, 98, 235, 86, 109, 197, 210, 145, 237, 23, 53, 98, 239, 130, 79, 230, 206, 138, 240, 234,
    99, 30, 222, 218, 49, 151, 100, 87, 104, 171, 26, 177, 154, 237, 160, 186, 58, 136, 50, 58,
    129, 81, 36, 127, 170, 208, 234, 49, 21, 56, 110, 135, 2, 202, 5, 126, 18, 193, 113, 117, 46,
    92, 173, 111, 240, 68, 71, 53, 134, 20, 71, 140, 209, 105, 137, 202, 213, 105, 21, 125, 138,
    22, 80, 231, 21, 114, 189, 75, 189, 79, 30, 192, 133, 88, 34, 90, 9, 26, 225, 105, 109, 106,
    141, 166, 200, 233, 154, 43, 110, 43, 14, 164, 201, 208, 35, 243, 86, 93, 176, 111, 70, 230,
    233, 141, 29, 171, 59, 35, 75, 245, 175, 216, 234, 234, 142, 153, 165, 119, 68, 44, 57, 35, 29,
    55, 183, 105, 105, 109, 47, 206, 50, 29, 38, 203, 8, 3, 111, 62, 78, 111, 182, 158, 178, 150,
    17, 252, 103, 189, 151, 89, 53, 101, 209, 239, 225, 162, 196, 252, 40, 85, 148, 241, 42, 76,
    235, 212, 84, 37, 156, 148, 146, 47, 98, 255, 192, 100, 177, 118, 204, 187, 252, 29, 189, 225,
    186, 182, 146, 47, 92, 87, 129, 152, 71, 220, 127, 134, 229, 241, 148, 135, 91, 80, 105, 34,
    86, 52, 223, 200, 218, 199, 93, 74, 242, 58, 22, 246, 85, 107, 199, 41, 73, 206, 3, 93, 217,
    151, 26, 180, 242, 110, 216, 119, 92, 247, 98, 119, 144, 16, 41, 178, 127, 249, 62, 116, 172,
    130, 10, 90, 34, 57, 126, 184, 38, 32, 144, 148, 175, 132, 160, 165, 135, 220, 158, 238, 196,
    207, 182, 75, 143, 138, 106, 254, 103, 87, 214, 48, 83, 168, 225, 242, 195, 74, 150, 221, 228,
    198, 215, 72, 172, 67, 37, 149, 58, 166, 172, 217, 58, 100, 52, 170, 62, 9, 221, 87, 245, 201,
    124, 140, 226, 185, 188, 198, 160, 158, 24, 199, 233, 188, 242, 24, 203, 55, 50, 131, 149, 124,
    132, 235, 62, 194, 154, 122, 19, 79, 6, 115, 16, 197, 234, 208, 218, 224, 19, 216, 162, 183,
    136, 152, 80, 128, 87, 68, 18, 211, 229, 44, 178, 21, 127, 170, 61, 202, 51, 21, 193, 95, 201,
    224, 47, 66, 52, 247, 45, 26, 41, 110, 140, 120, 51, 193, 201, 61, 44, 79, 214, 209, 47, 241,
    243, 229, 184, 163, 27, 201, 230, 231, 47, 59, 202, 203, 138, 151, 17, 9, 248, 228, 207, 22,
    57, 57, 202, 39, 197, 46, 142, 115, 89, 183, 205, 78, 142, 205, 25, 221, 94, 130, 111, 129,
    203, 201, 55, 106, 128, 150, 180, 78, 99, 211, 64, 246, 67, 148, 23, 107, 185, 177, 49, 14,
    195, 20, 176, 172, 156, 28, 143, 29, 60, 75, 227, 16, 10, 153, 0, 169, 176, 196, 182, 195, 66,
    248, 177, 110, 195, 54, 99, 30, 150, 73, 43, 70, 135, 33, 104, 184, 123, 176, 166, 13, 63, 51,
    200, 195, 163, 112, 119, 220, 114, 61, 81, 121, 27, 55, 22, 197, 152, 101, 125, 41, 201, 64,
    205, 41, 222, 184, 124, 188, 78, 125, 115, 5, 156, 107, 75, 125, 68, 35, 29, 198, 114, 194,
    204, 224, 225, 242, 208, 43, 74, 19, 24, 27, 12, 136, 224, 138, 42, 160, 204, 11, 126, 110,
    205, 200, 1, 6, 133, 120, 241, 236, 124, 200, 85, 196, 120, 33, 179, 85, 71, 6, 18, 207, 127,
    87, 158, 58, 75, 136, 211, 102, 193, 61, 20, 14, 40, 22, 130, 253, 1, 204, 67, 224, 137, 234,
    189, 196, 126, 167, 139, 131, 2, 94, 195, 69, 188, 51, 89, 47, 103, 101, 74, 54, 19, 178, 202,
    202, 6, 138, 161, 247, 155, 105, 145, 221, 168, 215, 10, 115, 39, 58, 48, 51, 111, 97, 136, 40,
    111, 131, 36, 57, 77, 108, 87, 18, 149, 191, 180, 173, 82, 51, 165, 49, 29, 43, 24, 213, 64,
    75, 170, 252, 208, 136, 70, 247, 199, 120, 151, 124, 36, 220, 138, 233, 27, 9, 15, 199, 87, 12,
    164, 68, 162, 116, 12, 149, 100, 248, 20, 44, 237, 132, 54, 135, 178, 18, 5, 203, 214, 104,
    159, 236, 246, 120, 122, 112, 1, 81, 171, 15, 157, 200, 57, 2, 250, 85, 32, 233, 231, 132, 116,
    94, 119, 148, 166, 167, 78, 14, 165, 191, 73, 205, 187, 248, 186, 73, 56, 230, 32, 124, 55,
    226, 109, 39, 230, 118, 154, 72, 14, 210, 246, 142, 43, 255, 145, 193, 222, 167, 230, 115, 138,
    173, 175, 161, 26, 139, 67, 202, 184, 223, 44, 57, 77, 37, 34, 199, 110, 181, 203, 40, 15, 164,
    71, 183, 40, 255, 55, 42, 240, 45, 17, 133, 23, 36, 212, 121, 165, 60, 37, 62, 171, 95, 226,
    43, 121, 157, 13, 191, 122, 199, 228, 183, 1, 14, 230, 191, 245, 124, 97, 160, 249, 142, 175,
    134, 44, 177, 44, 191, 220, 17, 89, 229, 156, 239, 163, 107, 102, 156, 223, 12, 127, 78, 211,
    208, 73, 1, 232, 239, 193, 208, 211, 15, 167, 79, 157, 40, 156, 155, 230, 241, 135, 237, 194,
    121, 199, 192, 238, 100, 17, 113, 127, 108, 83, 69, 54, 110, 59, 95, 66, 75, 96, 204, 29, 49,
    119, 134, 122, 205, 89, 78, 196, 161, 92, 39, 11, 101, 148, 218, 216, 45, 188, 126, 175, 216,
    222, 174, 179, 94, 51, 146, 164, 35, 38, 252, 86, 120, 10, 243, 44, 183, 23, 157, 92, 59, 28,
    144, 101, 87, 27, 98, 26, 94, 18, 184, 84, 249, 125, 245, 168, 68, 7, 239, 155, 175, 173, 46,
    178, 78, 64, 122, 177, 105, 65, 225, 246, 44, 205, 136, 188, 11, 93, 189, 187, 248, 50, 191,
    245, 155, 156, 196, 173, 2, 132, 74, 208, 129, 165, 134, 174, 153, 123, 195, 10, 221, 211, 62,
    199, 68, 53, 7, 77, 144, 59, 60, 118, 131, 182, 245, 182, 116, 59, 242, 154, 44, 178, 189, 27,
    77, 12, 168, 109, 108, 123, 154, 132, 226, 123, 170, 38, 67, 239, 237, 151, 76, 173, 56, 215,
    55, 45, 157, 123, 176, 183, 99, 238, 112, 189, 226, 44, 176, 30, 220, 159, 185, 238, 186, 240,
    86, 82, 250, 15, 52, 229, 146, 36, 218, 103, 95, 58, 224, 223, 234, 34, 141, 45, 149, 9, 46,
    83, 125, 134, 77, 113, 231, 237, 177, 150, 214, 164, 172, 128, 94, 135, 107, 242, 83, 151, 129,
    108, 39, 50, 149, 149, 89, 19, 242, 92, 162, 49, 188, 118, 127, 112, 124, 53, 132, 40, 54, 138,
    143, 242, 176, 226, 47, 142, 129, 124, 102, 29, 226, 204, 230, 2, 103, 32, 151, 151, 208, 255,
    186, 240, 42, 222, 70, 82, 54, 1, 21, 107, 69, 230, 180, 45, 82, 161, 31, 5, 54, 12, 205, 223,
    212, 51, 112, 174, 241, 208, 69, 134, 223, 223, 10, 182, 230, 187, 187, 185, 153, 2, 56, 126,
    39, 165, 165, 73, 57, 191, 98, 214, 222, 152, 45, 20, 187, 170, 10, 192, 90, 28, 191, 253, 143,
    253, 254, 91, 196, 141, 248, 107, 197, 72, 196, 116, 3, 167, 248, 34, 7, 60, 101, 196, 92, 38,
    216, 168, 42, 129, 112, 143, 134, 58, 250, 212, 46, 144, 238, 62, 213, 39, 193, 208, 196, 98,
    213, 175, 224, 179, 111, 200, 135, 52, 0, 145, 215, 146, 152, 67, 32, 146, 83, 77, 171, 51, 39,
    38, 199, 146, 94, 248, 204, 0, 11, 84, 208, 91, 41, 155, 143, 238, 150, 60, 144, 34, 68, 116,
    168, 182, 252, 35, 151, 40, 225, 242, 26, 96, 133, 40, 116, 7, 77, 60, 29, 219, 227, 143, 203,
    62, 223, 203, 75, 237, 183, 121, 107, 227, 52, 219, 39, 8, 157, 115, 101, 220, 151, 30, 127,
    192, 15, 206, 194, 232, 126, 65, 244, 17, 11, 252, 22, 202, 137, 54, 70, 97, 235, 195, 149,
    109, 78, 175, 219, 85, 231, 132, 90, 31, 98, 163, 112, 241, 144, 153, 208, 8, 74, 157, 6, 131,
    129, 242, 147, 96, 13, 35, 162, 167, 210, 250, 176, 231, 92, 91, 45, 183, 235, 226, 27, 236,
    114, 40, 236, 124, 245, 103, 80, 154, 214, 20, 210, 103, 213, 90, 82, 236, 164, 77, 90, 238,
    85, 165, 133, 182, 14, 62, 105, 97, 33, 191, 89, 92, 61, 143, 139, 15, 180, 50, 86, 52, 2, 123,
    81, 115, 167, 75, 7, 165, 53, 24, 164, 134, 223, 216, 109, 62, 16, 122, 144, 5, 47, 222, 200,
    250, 211, 171, 231, 125, 135, 168, 74, 250, 176, 52, 19, 208, 251, 192, 64, 112, 219, 41, 91,
    109, 225, 81, 122, 101, 42, 178, 174, 64, 33, 166, 194, 87, 228, 90, 57, 239, 119, 89, 197, 79,
    30, 106, 61, 34, 64, 5, 218, 117, 237, 18, 214, 96, 63, 0, 16, 178, 138, 130, 153, 5, 193, 175,
    199, 149, 157, 75, 166, 85, 99, 158, 44, 246, 113, 77, 91, 251, 220, 181, 182, 89, 199, 109,
    40, 142, 237, 99, 54, 107, 81, 226, 108, 237, 219, 14, 116, 106, 171, 171, 172, 159, 94, 203,
    73, 169, 31, 194, 150, 44, 91, 112, 151, 158, 64, 124, 66, 224, 206, 123, 246, 30, 76, 67, 202,
    142, 81, 228, 164, 118, 135, 233, 132, 66, 159, 227, 6, 240, 47, 213, 140, 224, 45, 125, 146,
    82, 52, 173, 86, 170, 117, 28, 84, 55, 128, 164, 65, 54, 86, 35, 15, 87, 195, 36, 47, 208, 171,
    99, 106, 169, 60, 97, 250, 18, 204, 125, 96, 202, 95, 126, 175, 187, 72, 132, 150, 91, 86, 27,
    203, 27, 54, 111, 69, 141, 223, 137, 105, 231, 189, 104, 23, 173, 84, 156, 78, 125, 245, 175,
    203, 171, 220, 254, 207, 198, 3, 130, 198, 7, 87, 54, 197, 112, 40, 80, 191, 97, 92, 26, 4,
    120, 92, 245, 40, 36, 191, 24, 36, 246, 191, 146, 241, 143, 65, 67, 56, 88, 142, 37, 155, 211,
    163, 50, 209, 173, 247, 98, 107, 134, 36, 43, 52, 32, 39, 41, 201, 4, 147, 142, 167, 13, 52,
    22, 249, 80, 175, 108, 208, 121, 69, 191, 184, 86, 220, 124, 82, 184, 204, 127, 172, 124, 40,
    35, 62, 73, 140, 47, 205, 153, 0, 149, 70, 183, 221, 13, 144, 225, 33, 11, 6, 179, 152, 184,
    233, 210, 165, 250, 114, 180, 118, 204, 85, 232, 96, 217, 97, 85, 234, 107, 229, 10, 172, 200,
    26, 117, 199, 254, 33, 1, 28, 154, 79, 124, 115, 114, 59, 142, 37, 179, 238, 38, 191, 77, 12,
    243, 117, 15, 213, 245, 142, 175, 163, 231, 235, 222, 40, 232, 63, 157, 52, 228, 198, 118, 111,
    208, 47, 51, 251, 87, 13, 87, 14, 224, 22, 114, 216, 109, 233, 6, 149, 194, 156, 238, 243, 49,
    96, 102, 101, 79, 86, 3, 58, 222, 156, 213, 253, 110, 117, 33, 53, 10, 109, 233, 11, 114, 107,
    210, 30,
];

#[cortex_m_rt::entry]
fn main() -> ! {
    use libcrux_ml_dsa::MLDSASigningKey;
    let signing_randomness = [4u8; 32];
    let message = [5u8; 2];
    let _signature = mldsa::sign(&MLDSASigningKey::new(SK), &message, b"", signing_randomness).unwrap();

    board::exit()
}
