use axum::{
    Router,
    extract::ws::{Message, WebSocket, WebSocketUpgrade},
    response::{Html, IntoResponse},
    routing::get,
};
use futures::{sink::SinkExt, stream::StreamExt};
use libcrux_ml_dsa::ml_dsa_65::MLDSA65SigningKey;
use libcrux_ml_kem::mlkem768::MlKem768Ciphertext;
use rand::TryRngCore;
use serde::{Deserialize, Serialize};
use std::{
    env,
    sync::{Arc, RwLock},
};

use tokio::sync::broadcast;
use tokio::time::{Duration, Instant, sleep, timeout};

const DASHBOARD_ADDRESS: &str = "127.0.0.1:3000";
const DEFAULT_TTY: &str = "/dev/ttyACM1";
const MLDSA_CONTEXT: &[u8; 16] = b"Libcrux-IoT Demo";

pub enum Error {
    InvalidSignature,
}

const SK: [u8; 4032] = [
    31, 37, 215, 153, 90, 137, 0, 82, 53, 54, 125, 134, 105, 73, 18, 130, 2, 190, 25, 213, 70, 233,
    166, 249, 140, 165, 134, 91, 115, 196, 53, 21, 81, 90, 152, 22, 158, 41, 12, 149, 151, 109,
    230, 150, 69, 81, 155, 209, 76, 183, 183, 137, 131, 131, 61, 136, 190, 89, 108, 119, 224, 192,
    25, 180, 183, 77, 167, 139, 21, 164, 120, 133, 24, 251, 83, 137, 32, 80, 196, 64, 111, 238, 48,
    135, 82, 177, 151, 173, 238, 89, 222, 164, 138, 237, 151, 228, 255, 115, 167, 101, 103, 202,
    71, 15, 83, 125, 49, 254, 139, 159, 151, 171, 49, 93, 12, 167, 87, 63, 174, 200, 189, 93, 208,
    107, 53, 243, 123, 206, 103, 135, 68, 6, 6, 37, 22, 67, 82, 96, 20, 56, 99, 100, 32, 83, 118,
    119, 116, 120, 132, 115, 21, 133, 18, 84, 24, 112, 20, 65, 134, 98, 40, 52, 52, 55, 37, 136,
    85, 53, 52, 129, 117, 80, 119, 134, 113, 101, 6, 97, 81, 84, 40, 84, 84, 103, 16, 38, 49, 51,
    113, 97, 86, 3, 82, 66, 114, 120, 88, 114, 16, 64, 5, 69, 71, 2, 50, 40, 129, 117, 53, 23, 104,
    37, 21, 4, 120, 88, 32, 98, 120, 117, 3, 6, 33, 48, 52, 67, 70, 131, 68, 82, 24, 21, 134, 98,
    32, 66, 54, 24, 20, 18, 131, 98, 80, 118, 19, 97, 133, 117, 100, 131, 48, 37, 18, 64, 68, 119,
    104, 48, 48, 36, 22, 132, 48, 70, 134, 37, 102, 65, 34, 5, 23, 103, 81, 112, 88, 114, 99, 69,
    136, 119, 55, 68, 119, 3, 68, 128, 99, 22, 68, 132, 1, 102, 71, 96, 64, 99, 86, 35, 34, 65, 50,
    16, 5, 118, 118, 87, 86, 114, 118, 88, 65, 96, 6, 6, 130, 40, 23, 118, 120, 67, 70, 38, 87,
    120, 116, 99, 38, 68, 53, 65, 24, 103, 115, 1, 132, 51, 23, 82, 120, 115, 16, 86, 37, 3, 87,
    132, 38, 5, 114, 1, 1, 133, 113, 54, 22, 115, 70, 33, 114, 16, 34, 56, 84, 131, 8, 16, 97, 8,
    99, 52, 48, 69, 3, 87, 134, 82, 98, 51, 21, 71, 86, 20, 37, 119, 98, 33, 69, 1, 85, 116, 68,
    51, 101, 72, 38, 120, 70, 118, 120, 54, 118, 135, 86, 32, 40, 120, 22, 53, 103, 51, 98, 98, 5,
    85, 88, 102, 67, 24, 104, 115, 37, 38, 112, 115, 85, 103, 40, 64, 68, 0, 49, 7, 2, 133, 71,
    128, 67, 66, 98, 67, 86, 20, 81, 102, 19, 134, 24, 80, 86, 135, 50, 120, 39, 98, 120, 97, 102,
    34, 112, 85, 115, 3, 128, 101, 20, 65, 132, 130, 114, 100, 55, 115, 2, 135, 24, 99, 117, 50,
    80, 115, 69, 118, 116, 19, 37, 136, 64, 131, 134, 54, 69, 0, 72, 136, 53, 132, 84, 24, 52, 5,
    88, 64, 84, 53, 135, 3, 133, 130, 114, 17, 66, 51, 65, 5, 52, 1, 32, 97, 115, 16, 72, 115, 17,
    67, 86, 51, 18, 101, 8, 1, 131, 102, 22, 71, 34, 116, 37, 34, 20, 104, 81, 131, 50, 85, 50,
    114, 7, 82, 40, 129, 83, 71, 115, 104, 118, 102, 1, 20, 70, 96, 33, 4, 112, 114, 16, 128, 38,
    4, 52, 38, 104, 131, 52, 48, 133, 18, 128, 119, 84, 128, 17, 50, 86, 84, 68, 120, 36, 132, 2,
    38, 50, 36, 113, 88, 80, 113, 18, 118, 133, 85, 119, 22, 104, 0, 69, 115, 96, 96, 102, 21, 50,
    66, 129, 33, 81, 103, 39, 68, 119, 128, 115, 112, 72, 5, 52, 132, 96, 128, 17, 8, 96, 65, 101,
    97, 35, 87, 135, 71, 4, 134, 136, 112, 86, 37, 64, 117, 18, 21, 132, 37, 119, 135, 51, 68, 101,
    98, 117, 4, 96, 120, 132, 32, 72, 3, 51, 19, 64, 40, 8, 8, 18, 0, 68, 113, 7, 35, 100, 5, 22,
    98, 83, 52, 17, 18, 5, 64, 70, 34, 129, 132, 4, 39, 87, 100, 128, 22, 1, 117, 52, 96, 3, 133,
    81, 5, 16, 52, 130, 82, 136, 4, 87, 33, 34, 129, 40, 69, 117, 7, 37, 34, 130, 86, 116, 65, 120,
    82, 70, 129, 84, 22, 56, 82, 35, 87, 18, 136, 96, 116, 17, 50, 5, 7, 2, 37, 4, 135, 5, 100,
    100, 83, 33, 20, 133, 22, 119, 22, 83, 7, 52, 69, 40, 120, 113, 104, 116, 2, 71, 54, 97, 80,
    117, 113, 132, 53, 3, 103, 33, 49, 104, 66, 66, 22, 34, 3, 135, 19, 134, 115, 8, 49, 56, 119,
    35, 115, 40, 5, 32, 85, 7, 18, 17, 32, 130, 68, 98, 131, 100, 85, 112, 50, 71, 3, 54, 98, 64,
    17, 33, 53, 97, 83, 1, 102, 129, 32, 70, 86, 34, 80, 52, 131, 117, 82, 48, 136, 22, 102, 16,
    24, 133, 24, 68, 48, 69, 136, 6, 130, 96, 99, 136, 16, 85, 71, 114, 84, 48, 104, 84, 84, 32,
    117, 50, 65, 96, 16, 117, 114, 19, 8, 65, 136, 70, 119, 103, 16, 114, 55, 119, 35, 84, 36, 81,
    54, 86, 50, 56, 96, 1, 40, 100, 119, 64, 88, 0, 19, 52, 64, 82, 81, 104, 21, 35, 68, 54, 48,
    117, 99, 52, 33, 131, 119, 132, 32, 99, 120, 24, 84, 97, 114, 65, 2, 114, 128, 53, 1, 6, 103,
    50, 97, 49, 115, 120, 120, 32, 1, 65, 81, 66, 0, 83, 129, 129, 33, 112, 88, 34, 52, 100, 22,
    82, 113, 88, 8, 64, 1, 51, 18, 37, 22, 120, 65, 132, 102, 54, 52, 69, 103, 2, 7, 103, 85, 96,
    80, 88, 1, 65, 86, 48, 36, 71, 67, 87, 36, 114, 87, 86, 1, 2, 19, 32, 21, 7, 32, 128, 54, 97,
    132, 96, 49, 119, 88, 83, 72, 5, 132, 33, 68, 49, 55, 80, 80, 112, 3, 119, 116, 2, 72, 36, 102,
    21, 32, 4, 84, 117, 36, 131, 100, 36, 33, 54, 99, 72, 119, 82, 24, 99, 3, 69, 39, 118, 136, 55,
    0, 102, 65, 56, 19, 52, 102, 83, 40, 66, 6, 53, 17, 23, 5, 97, 113, 24, 4, 98, 23, 40, 6, 88,
    65, 135, 84, 117, 65, 50, 16, 66, 19, 17, 103, 87, 5, 101, 85, 70, 35, 6, 102, 116, 102, 80,
    80, 87, 8, 131, 99, 23, 17, 35, 132, 81, 49, 20, 17, 97, 88, 18, 66, 130, 119, 119, 83, 128,
    19, 132, 64, 80, 86, 39, 39, 6, 56, 129, 21, 80, 82, 33, 85, 40, 71, 66, 32, 117, 7, 128, 98,
    86, 133, 2, 115, 72, 7, 3, 3, 117, 33, 8, 69, 16, 39, 103, 40, 113, 132, 101, 3, 16, 88, 0,
    100, 112, 87, 53, 130, 88, 101, 101, 104, 68, 20, 84, 104, 115, 85, 120, 52, 96, 53, 100, 8,
    65, 131, 70, 71, 117, 8, 119, 64, 133, 83, 72, 120, 81, 98, 40, 84, 134, 115, 17, 55, 7, 135,
    53, 20, 7, 88, 54, 69, 33, 103, 56, 119, 38, 21, 55, 130, 96, 22, 21, 7, 69, 128, 82, 5, 32,
    55, 39, 115, 69, 22, 21, 51, 65, 37, 135, 115, 48, 120, 115, 101, 49, 116, 87, 88, 55, 96, 134,
    118, 104, 130, 87, 87, 130, 116, 65, 34, 54, 88, 70, 2, 6, 55, 7, 112, 2, 119, 118, 103, 22,
    18, 36, 39, 23, 19, 97, 3, 85, 100, 103, 53, 48, 17, 117, 3, 101, 119, 81, 54, 64, 23, 18, 33,
    68, 6, 100, 98, 23, 54, 71, 54, 136, 18, 20, 84, 53, 87, 34, 34, 132, 69, 54, 49, 23, 3, 128,
    133, 103, 39, 2, 17, 22, 70, 130, 16, 114, 96, 136, 114, 69, 117, 67, 49, 18, 34, 116, 97, 0,
    49, 101, 87, 2, 69, 81, 72, 21, 3, 85, 88, 48, 103, 85, 68, 35, 134, 101, 6, 39, 34, 2, 48,
    120, 87, 101, 101, 68, 134, 117, 102, 84, 96, 129, 50, 115, 0, 71, 84, 56, 53, 17, 48, 51, 131,
    54, 24, 40, 87, 5, 130, 115, 51, 96, 1, 8, 87, 136, 136, 134, 134, 85, 20, 87, 64, 88, 7, 71,
    56, 65, 71, 65, 20, 80, 83, 114, 87, 134, 2, 16, 102, 40, 82, 8, 115, 86, 84, 102, 118, 69, 50,
    53, 70, 50, 6, 97, 51, 48, 128, 3, 84, 86, 24, 102, 82, 101, 39, 39, 115, 83, 7, 55, 55, 34,
    38, 56, 86, 38, 114, 2, 68, 33, 3, 17, 38, 120, 119, 53, 65, 18, 81, 84, 133, 67, 71, 85, 82,
    113, 120, 32, 5, 113, 7, 118, 119, 85, 120, 72, 100, 3, 97, 132, 112, 22, 0, 5, 134, 112, 19,
    80, 6, 65, 88, 80, 6, 51, 32, 136, 32, 6, 112, 20, 36, 2, 131, 130, 0, 118, 116, 117, 112, 132,
    65, 6, 72, 118, 20, 131, 16, 96, 4, 56, 18, 112, 53, 136, 49, 66, 130, 36, 99, 82, 101, 239,
    62, 86, 189, 144, 174, 142, 25, 45, 255, 232, 240, 36, 183, 216, 49, 103, 139, 64, 144, 93,
    203, 137, 21, 25, 176, 68, 42, 83, 119, 159, 39, 4, 148, 51, 92, 12, 158, 239, 176, 181, 162,
    191, 243, 102, 195, 158, 104, 0, 78, 74, 170, 150, 155, 248, 235, 29, 109, 13, 54, 255, 169,
    110, 217, 246, 41, 64, 170, 82, 88, 176, 22, 207, 126, 162, 241, 254, 170, 7, 142, 196, 34, 30,
    25, 62, 88, 177, 169, 1, 229, 250, 122, 96, 200, 183, 137, 137, 229, 132, 68, 235, 19, 128, 27,
    241, 61, 107, 159, 4, 75, 188, 48, 241, 156, 26, 225, 138, 203, 39, 156, 76, 91, 59, 13, 205,
    7, 157, 15, 118, 30, 81, 20, 90, 226, 41, 255, 207, 150, 215, 61, 74, 180, 133, 64, 167, 125,
    188, 177, 184, 209, 32, 84, 52, 209, 7, 146, 190, 8, 154, 227, 255, 168, 16, 32, 242, 176, 176,
    199, 77, 250, 107, 94, 215, 18, 160, 234, 40, 239, 212, 241, 1, 251, 58, 168, 226, 40, 251, 77,
    207, 86, 11, 114, 126, 239, 32, 160, 175, 70, 137, 155, 138, 241, 46, 155, 170, 152, 64, 153,
    61, 128, 72, 109, 146, 115, 13, 33, 233, 107, 38, 247, 122, 102, 138, 25, 137, 62, 18, 233, 85,
    83, 14, 194, 78, 210, 146, 94, 21, 9, 112, 41, 8, 210, 229, 92, 218, 54, 165, 92, 29, 195, 47,
    165, 87, 66, 24, 190, 160, 163, 65, 191, 197, 166, 149, 216, 253, 36, 111, 74, 68, 20, 202,
    221, 84, 63, 227, 241, 194, 61, 194, 172, 102, 8, 207, 43, 43, 248, 33, 107, 97, 203, 129, 70,
    191, 251, 72, 161, 26, 49, 56, 154, 27, 99, 80, 39, 235, 176, 247, 154, 220, 142, 127, 222,
    104, 172, 125, 43, 59, 21, 162, 49, 178, 67, 70, 2, 102, 60, 93, 76, 65, 27, 184, 127, 233,
    146, 28, 29, 16, 162, 197, 125, 116, 175, 68, 162, 23, 5, 21, 188, 217, 145, 44, 125, 213, 27,
    88, 208, 244, 57, 250, 230, 102, 229, 35, 92, 29, 192, 213, 122, 7, 25, 179, 32, 230, 204, 39,
    238, 182, 228, 109, 96, 42, 121, 92, 202, 97, 255, 227, 148, 99, 66, 151, 220, 71, 56, 123,
    158, 32, 78, 172, 99, 120, 214, 194, 201, 31, 48, 144, 208, 102, 66, 13, 49, 41, 155, 33, 190,
    82, 83, 70, 211, 8, 161, 89, 0, 123, 68, 103, 87, 116, 150, 171, 121, 23, 239, 53, 49, 191,
    195, 117, 174, 4, 40, 108, 36, 41, 173, 138, 237, 172, 12, 187, 91, 97, 198, 111, 78, 200, 68,
    134, 125, 78, 13, 224, 43, 72, 254, 163, 231, 86, 41, 113, 206, 124, 42, 198, 117, 144, 48, 83,
    137, 228, 95, 221, 143, 226, 153, 71, 139, 64, 178, 15, 46, 206, 70, 114, 1, 155, 107, 20, 233,
    244, 56, 240, 50, 63, 27, 143, 103, 206, 47, 96, 189, 123, 243, 82, 38, 4, 110, 185, 80, 220,
    105, 223, 116, 73, 53, 87, 73, 148, 89, 224, 154, 17, 217, 179, 46, 86, 117, 4, 102, 2, 253,
    210, 28, 115, 57, 102, 247, 202, 226, 215, 57, 193, 202, 247, 128, 51, 254, 157, 183, 76, 25,
    44, 250, 196, 179, 221, 200, 152, 177, 232, 223, 121, 65, 3, 186, 155, 141, 13, 22, 144, 91,
    149, 141, 128, 254, 127, 33, 59, 2, 139, 99, 113, 124, 157, 3, 138, 177, 194, 125, 221, 188,
    32, 218, 66, 249, 180, 109, 71, 71, 17, 154, 182, 67, 34, 110, 56, 72, 170, 100, 201, 7, 183,
    72, 83, 218, 96, 115, 67, 206, 43, 185, 156, 153, 62, 164, 86, 8, 147, 79, 168, 3, 196, 130,
    116, 121, 93, 166, 153, 195, 131, 252, 57, 128, 98, 84, 156, 26, 200, 58, 119, 185, 149, 21,
    174, 243, 205, 140, 93, 59, 139, 210, 196, 234, 162, 191, 182, 218, 12, 62, 6, 110, 32, 205,
    185, 126, 133, 124, 56, 192, 67, 69, 110, 217, 242, 255, 56, 32, 153, 105, 29, 163, 103, 70,
    77, 210, 96, 42, 116, 11, 48, 210, 78, 237, 245, 90, 13, 86, 194, 183, 130, 68, 139, 115, 63,
    80, 154, 186, 204, 22, 208, 142, 56, 125, 15, 228, 125, 46, 99, 127, 136, 95, 163, 183, 176,
    145, 68, 20, 210, 37, 84, 222, 247, 209, 48, 83, 219, 143, 73, 127, 250, 65, 159, 21, 145, 221,
    214, 241, 97, 157, 122, 153, 200, 180, 54, 41, 71, 91, 221, 34, 85, 124, 9, 83, 46, 67, 146,
    72, 80, 229, 182, 74, 174, 117, 14, 153, 146, 114, 182, 14, 99, 119, 143, 191, 178, 251, 115,
    64, 225, 142, 111, 47, 230, 235, 134, 21, 152, 9, 193, 218, 104, 112, 162, 111, 16, 196, 11,
    223, 129, 23, 120, 65, 76, 155, 83, 4, 19, 105, 121, 72, 102, 82, 110, 153, 122, 217, 63, 159,
    112, 131, 64, 176, 106, 196, 42, 76, 255, 26, 71, 61, 116, 193, 113, 106, 60, 234, 225, 202,
    151, 92, 119, 60, 138, 179, 177, 114, 120, 67, 167, 138, 125, 212, 104, 25, 127, 205, 196, 138,
    223, 174, 90, 133, 214, 217, 145, 213, 188, 119, 64, 237, 238, 245, 119, 219, 40, 65, 58, 175,
    89, 52, 6, 229, 124, 147, 213, 30, 222, 253, 21, 133, 29, 110, 207, 232, 136, 251, 122, 144,
    235, 47, 182, 157, 229, 158, 2, 135, 105, 94, 195, 87, 36, 50, 198, 129, 18, 13, 184, 252, 113,
    193, 242, 115, 243, 11, 254, 45, 17, 192, 73, 43, 223, 246, 104, 89, 43, 84, 29, 237, 120, 54,
    174, 243, 9, 12, 25, 239, 177, 244, 0, 241, 230, 253, 152, 100, 56, 133, 75, 108, 237, 160, 62,
    72, 254, 246, 31, 80, 151, 84, 239, 154, 179, 89, 117, 205, 87, 16, 101, 51, 98, 97, 3, 87,
    252, 76, 46, 214, 154, 110, 104, 105, 107, 23, 170, 179, 223, 96, 133, 194, 198, 28, 8, 99,
    138, 226, 157, 76, 14, 17, 187, 46, 189, 156, 239, 240, 60, 14, 125, 47, 53, 136, 129, 42, 243,
    244, 235, 65, 73, 74, 176, 179, 63, 77, 55, 52, 206, 196, 250, 20, 8, 9, 219, 16, 192, 200,
    211, 80, 96, 242, 182, 109, 52, 233, 165, 203, 224, 127, 2, 18, 15, 40, 195, 48, 141, 238, 47,
    253, 251, 182, 75, 1, 218, 53, 106, 52, 189, 239, 169, 35, 57, 21, 203, 40, 15, 44, 253, 47,
    199, 88, 145, 187, 208, 88, 128, 224, 54, 26, 84, 142, 246, 179, 15, 228, 81, 23, 79, 113, 6,
    73, 221, 98, 29, 204, 174, 128, 192, 88, 107, 129, 144, 239, 40, 167, 23, 219, 150, 117, 13,
    36, 203, 97, 9, 85, 140, 209, 4, 201, 169, 132, 158, 150, 66, 252, 11, 82, 191, 209, 108, 67,
    33, 19, 70, 91, 77, 28, 140, 97, 64, 182, 136, 213, 233, 231, 138, 60, 56, 161, 150, 182, 224,
    247, 107, 24, 76, 111, 186, 164, 141, 224, 255, 218, 14, 250, 88, 27, 36, 116, 167, 144, 42,
    27, 165, 26, 215, 191, 196, 81, 27, 227, 163, 100, 42, 174, 47, 122, 113, 215, 236, 129, 178,
    102, 146, 240, 93, 18, 222, 248, 232, 95, 107, 209, 93, 200, 138, 30, 128, 39, 235, 6, 175, 76,
    221, 181, 53, 166, 252, 76, 4, 54, 43, 133, 221, 131, 129, 196, 203, 84, 184, 38, 180, 106, 90,
    219, 225, 255, 94, 236, 218, 233, 41, 130, 76, 77, 74, 113, 210, 64, 96, 37, 234, 251, 73, 14,
    120, 84, 0, 236, 152, 240, 70, 9, 94, 140, 253, 113, 184, 141, 161, 7, 203, 87, 107, 91, 150,
    255, 133, 0, 47, 231, 3, 88, 177, 241, 132, 244, 249, 252, 242, 125, 125, 23, 155, 46, 209, 80,
    251, 113, 177, 46, 224, 144, 201, 158, 233, 10, 236, 232, 180, 80, 0, 123, 70, 142, 139, 242,
    234, 175, 55, 212, 48, 245, 6, 38, 174, 242, 80, 123, 252, 47, 84, 89, 240, 97, 236, 173, 33,
    88, 79, 4, 181, 41, 192, 161, 91, 194, 245, 68, 251, 189, 161, 130, 129, 240, 243, 48, 135, 83,
    250, 159, 121, 129, 234, 243, 216, 235, 193, 127, 64, 66, 106, 30, 246, 56, 44, 89, 106, 55,
    159, 249, 106, 67, 99, 81, 106, 128, 72, 188, 196, 167, 16, 5, 38, 174, 228, 111, 226, 143,
    204, 7, 218, 29, 226, 221, 53, 222, 193, 197, 242, 242, 234, 222, 51, 105, 47, 119, 125, 104,
    124, 176, 170, 230, 15, 224, 214, 53, 8, 182, 65, 171, 221, 105, 36, 48, 251, 245, 212, 193,
    70, 81, 255, 183, 214, 241, 26, 215, 154, 84, 220, 193, 236, 209, 120, 31, 225, 19, 114, 155,
    95, 211, 106, 130, 100, 186, 3, 193, 24, 209, 234, 82, 109, 249, 221, 81, 106, 3, 226, 133, 99,
    85, 201, 59, 201, 225, 70, 203, 45, 177, 249, 117, 182, 16, 253, 180, 194, 252, 114, 242, 128,
    118, 188, 203, 174, 8, 116, 4, 173, 228, 94, 20, 241, 127, 108, 188, 70, 5, 211, 35, 195, 234,
    4, 224, 150, 119, 196, 40, 118, 107, 7, 171, 153, 90, 243, 107, 203, 71, 178, 251, 184, 76, 98,
    14, 208, 104, 45, 166, 121, 226, 135, 96, 76, 51, 96, 24, 54, 102, 210, 62, 3, 160, 164, 189,
    56, 96, 217, 123, 142, 235, 6, 183, 197, 9, 210, 204, 24, 80, 20, 125, 162, 179, 128, 228, 62,
    124, 212, 155, 124, 108, 101, 13, 147, 5, 249, 171, 119, 94, 1, 84, 203, 104, 12, 60, 171, 152,
    50, 249, 224, 63, 181, 80, 127, 228, 178, 205, 53, 24, 208, 229, 28, 122, 78, 122, 56, 176, 72,
    49, 11, 37, 233, 32, 171, 30, 57, 169, 122, 193, 195, 214, 154, 163, 55, 170, 115, 162, 225,
    175, 67, 89, 46, 17, 66, 200, 111, 38, 116, 214, 53, 193, 214, 238, 46, 216, 135, 170, 102,
    177, 93, 160, 30, 42, 46, 178, 111, 88, 105, 123, 86, 224, 169, 230, 36, 92, 230, 37, 138, 17,
    45, 49, 210, 48, 63, 49, 142, 227, 103, 200, 69, 70, 88, 192, 224, 70, 123, 100, 54, 223, 218,
    72, 239, 172, 183, 250, 43, 188, 162, 66, 167, 200, 134, 242, 233, 16, 46, 161, 90, 159, 160,
    142, 109, 155, 202, 170, 227, 218, 212, 121, 205, 170, 169, 234, 181, 19, 59, 176, 67, 103, 26,
    7, 24, 134, 184, 119, 247, 89, 97, 225, 185, 241, 108, 139, 47, 154, 86, 97, 37, 21, 228, 21,
    225, 234, 92, 79, 117, 60, 136, 232, 56, 31, 133, 18, 72, 251, 16, 134, 206, 164, 252, 3, 152,
    23, 121, 23, 38, 145, 16, 75, 73, 142, 213, 87, 207, 44, 208, 230, 192, 33, 39, 229, 222, 241,
    177, 50, 210, 249, 18, 20, 158, 170, 109, 157, 95, 99, 36, 160, 146, 220, 231, 169, 154, 209,
    219, 150, 147, 193, 120, 168, 94, 240, 10, 90, 132, 10, 76, 38, 1, 194, 167, 132, 68, 131, 192,
    98, 206, 197, 19, 95, 216, 241, 124, 237, 179, 238, 45, 222, 66, 248, 250, 14, 236, 116, 10,
    114, 238, 151, 140, 199, 190, 64, 84, 101, 112, 206, 59, 197, 110, 93, 140, 245, 123, 80, 206,
    74, 25, 243, 157, 135, 110, 13, 70, 225, 69, 184, 147, 133, 163, 200, 91, 198, 32, 189, 186,
    209, 46, 118, 134, 64, 98, 180, 48, 148, 184, 184, 197, 32, 150, 107, 46, 189, 122, 78, 167,
    148, 185, 211, 26, 88, 102, 49, 59, 242, 88, 19, 219, 50, 98, 38, 204, 128, 4, 154, 217, 212,
    174, 38, 180, 154, 177, 7, 66, 114, 50, 68, 52, 186, 142, 163, 24, 238, 200, 106, 179, 231,
    193, 119, 41, 168, 108, 59, 234, 158, 37, 96, 25, 243, 240, 67, 33, 177, 175, 134, 90, 173, 7,
    191, 125, 121, 59, 247, 161, 251, 45, 220, 152, 242, 97, 195, 159, 114, 115, 198, 75, 191, 191,
    109, 241, 138, 161, 141, 218, 44, 115, 230, 131, 131, 36, 236, 158, 58, 198, 180, 152, 233,
    149, 26, 14, 66, 52, 227, 68, 215, 102, 195, 201, 65, 218, 47, 156, 149, 151, 240, 132, 6, 9,
    199, 128, 151, 187, 112, 156, 138, 209, 55, 32, 73, 203, 219, 189, 191, 0, 43, 36, 60, 10, 17,
    134, 97, 119, 104, 76, 140, 242, 237, 97, 147, 88, 98, 107, 76, 43, 211, 161, 208, 249, 178,
    247, 192, 193, 213, 218, 66, 191, 147, 73, 183, 47, 228, 77, 145, 128, 252, 0, 144, 27, 84, 35,
    118, 194, 3, 143, 78, 120, 73, 95, 66, 245, 92, 161, 70, 136, 81, 22, 255, 22, 172, 49, 135,
    88, 104, 60, 106, 53, 89, 157, 203, 223, 224, 22, 191, 102, 158, 144, 73, 109, 88, 128, 107,
    223, 83, 94, 27, 106, 109, 5, 216, 245, 101, 69, 147, 169, 3, 100, 175, 114, 131, 135, 227,
    137, 103, 225, 160, 59, 138, 111, 129, 234, 228, 218, 227, 185, 3, 227, 232, 117, 73, 153, 133,
    24, 29, 166, 16, 178, 211, 83, 11, 66, 194, 143, 48, 191, 33, 138, 237, 59, 104, 73, 86, 59,
    90, 207, 6, 23, 62, 147, 255, 196, 162, 119, 189, 108, 160, 250, 204, 20, 77, 235, 225, 121,
    186, 42, 210, 3, 124, 187, 220, 160, 74, 203, 229, 240, 90, 50, 100, 250, 105, 18, 216, 232,
    42, 228, 88, 53, 46, 217, 77, 48, 147, 147, 77, 98, 82, 206, 200, 0, 37, 186, 246, 84, 236,
    106, 114, 156, 176, 253, 214, 199, 126, 190, 249, 88, 216, 182, 114, 27, 124, 46, 94, 10, 254,
    123, 79, 255, 161, 207, 2, 16, 244, 63, 80, 33, 3, 42, 227, 214, 93, 153, 22, 212, 211, 142,
    175, 108, 212, 153, 70, 201, 252, 165, 95, 126, 7, 83, 210, 247, 146, 0, 114, 255, 56, 37, 93,
    150, 137, 208, 242, 195, 38, 89, 99, 3, 235, 85, 122, 55, 84, 111, 173, 150, 227, 85, 169, 117,
    91, 144, 221, 109, 242, 81, 206, 250, 162, 35, 112, 53, 0, 142, 13, 81, 40, 49, 174, 13, 60,
    229, 10, 206, 50, 43, 201, 181, 95, 31, 228, 227, 229, 159, 122, 115, 245, 234, 78, 248, 208,
    248, 159, 114, 181, 72, 118, 169, 82, 252, 10, 49, 9, 197, 97, 219, 159, 125, 47, 201, 11, 178,
    213, 76, 53, 150, 201, 247, 199, 49, 77, 80, 188, 236, 60, 177, 55, 254, 42, 22, 168, 88, 63,
    59, 134, 230, 231,
];
// --- Data Structures ---

#[derive(Clone, Serialize, Debug)]
struct ConnectionStats {
    rtt_ms: f64,
    payload_size: usize,
    success: bool,
    is_logical_error: bool, // New: true if response is "Connection failed"
}

struct AppState {
    sk: MLDSA65SigningKey,
    tty_path: String,
    simulate_error: bool,
}

// JSON message sent from Browser -> Rust
#[derive(Deserialize)]
#[serde(tag = "type", content = "value")]
enum ClientCommand {
    UpdatePayload(String),
    ToggleFail(bool),
}

type SharedState = Arc<RwLock<AppState>>;

#[tokio::main]
async fn main() {
    let mut args = env::args();
    let tty_path = args.nth(1).unwrap_or_else(|| DEFAULT_TTY.into());

    let (tx, _rx) = broadcast::channel::<ConnectionStats>(100);
    let tx_shared = Arc::new(tx);

    // Initialize State
    let state = Arc::new(RwLock::new(AppState {
        sk: MLDSA65SigningKey::new(SK),
        tty_path: tty_path.to_string(),
        simulate_error: false,
    }));

    // 1. Pinger Task
    let tx_pinger = tx_shared.clone();
    let state_pinger = state.clone();
    tokio::spawn(async move {
        loop {
            signed_ping(&tx_pinger, &state_pinger).await;
            sleep(Duration::from_millis(1000)).await;
        }
    });

    // 2. Web Server
    let app = Router::new().route("/", get(index_handler)).route(
        "/ws",
        get(move |ws: WebSocketUpgrade| {
            let tx = tx_shared.clone();
            let state = state.clone();
            async move { ws.on_upgrade(move |socket| websocket_handler(socket, tx, state)) }
        }),
    );

    println!("Dashboard running at http://{}", DASHBOARD_ADDRESS);
    let listener = tokio::net::TcpListener::bind(DASHBOARD_ADDRESS)
        .await
        .unwrap();
    axum::serve(listener, app).await.unwrap();
}

async fn signed_ping(tx: &Arc<broadcast::Sender<ConnectionStats>>, state: &SharedState) {
    // Determine what to send based on state
    let (sk, tty_path, is_forcing_fail) = {
        let guard = state.read().unwrap();
        (
            guard.sk.clone(),
            guard.tty_path.clone(),
            guard.simulate_error,
        )
    };

    let start = Instant::now();

    // Perform TCP Request
    let result = timeout(Duration::from_millis(1000), async {
        let mut port = serialport::new(tty_path, 115_200)
            .timeout(Duration::from_millis(100))
            .open()
            .expect("Failed to open port");

        // Generate an ML-KEM key pair.
        let mut rng = rand::rngs::OsRng;
        let mut mlkem_key_generation_randomness = [0u8; libcrux_ml_kem::KEY_GENERATION_SEED_SIZE];
        rng.try_fill_bytes(&mut mlkem_key_generation_randomness)
            .unwrap();
        let key_pair = libcrux_ml_kem::mlkem768::generate_key_pair(mlkem_key_generation_randomness);

        // Sign the encapsulation key.
        let mut signing_randomness = [0u8; libcrux_ml_dsa::SIGNING_RANDOMNESS_SIZE];
        rng.try_fill_bytes(&mut signing_randomness).unwrap();

        let mut signature = libcrux_ml_dsa::ml_dsa_65::sign(
            &sk,
            key_pair.public_key().as_slice(),
            MLDSA_CONTEXT,
            signing_randomness,
        )
        .unwrap();

        if is_forcing_fail {
            signature.as_mut_slice()[0] = !signature.as_mut_slice()[0];
        }

        // Send the host message.
        port.write_all(key_pair.public_key().as_slice())
            .expect("write failed");
        port.flush().unwrap();
        port.write_all(signature.as_slice()).expect("write failed");
        port.flush().unwrap();

        // Receive the client response.
        let mut response = [0u8; MlKem768Ciphertext::len() + 64];
        port.read_exact(&mut response).unwrap();
        port.flush().unwrap();

        if &response[0..64] == &[0u8; 64] {
            return Err::<[u8; 32], Error>(Error::InvalidSignature);
        };

        let encapsulation = libcrux_ml_kem::mlkem768::MlKem768Ciphertext::try_from(
            &response[64..libcrux_ml_kem::mlkem768::MlKem768Ciphertext::len() + 64],
        )
        .unwrap();

        let shared_secret =
            libcrux_ml_kem::mlkem768::decapsulate(key_pair.private_key(), &encapsulation);

        Ok::<[u8; 32], Error>(shared_secret)
    })
    .await;

    // Process Result
    let (is_logical_error, _shared_secret) = match result {
        Ok(Ok(shared_secret)) => {
            println!(
                "Received encapsulation of shared secret: {:?}",
                shared_secret
            );
            (true, shared_secret)
        }
        Ok(Err(_)) => (false, [0u8; 32]),
        _ => todo!(),
    };

    let stats = ConnectionStats {
        rtt_ms: start.elapsed().as_secs_f64() * 1000.0,
        payload_size: libcrux_ml_kem::mlkem768::MlKem768Ciphertext::len(),
        success: true,
        is_logical_error,
    };

    let _ = tx.send(stats);
}

// --- WebSocket Logic ---

async fn websocket_handler(
    socket: WebSocket,
    tx: Arc<broadcast::Sender<ConnectionStats>>,
    state: SharedState,
) {
    let (mut sender, mut receiver) = socket.split();
    let mut rx_stats = tx.subscribe();

    // Send Stats -> Browser
    let mut send_task = tokio::spawn(async move {
        while let Ok(stats) = rx_stats.recv().await {
            let json = serde_json::to_string(&stats).unwrap();
            if sender.send(Message::Text(json)).await.is_err() {
                break;
            }
        }
    });

    // Receive Commands -> Rust
    let mut recv_task = tokio::spawn(async move {
        while let Some(Ok(msg)) = receiver.next().await {
            if let Message::Text(text) = msg {
                if let Ok(cmd) = serde_json::from_str::<ClientCommand>(&text) {
                    let mut guard = state.write().unwrap();
                    match cmd {
                        ClientCommand::UpdatePayload(new_text) => {
                            println!("Payload updated: {}", new_text);
                            guard.tty_path = new_text;
                        }
                        ClientCommand::ToggleFail(force_fail) => {
                            println!("Force Fail mode set to: {}", force_fail);
                            guard.simulate_error = force_fail;
                        }
                    }
                }
            }
        }
    });

    tokio::select! {
        _ = (&mut send_task) => recv_task.abort(),
        _ = (&mut recv_task) => send_task.abort(),
    }
}

async fn index_handler() -> impl IntoResponse {
    Html(DASHBOARD_HTML)
}

const DASHBOARD_HTML: &str = r###"
<!DOCTYPE html>
<html>
<head>
    <title>Board Dashboard</title>
    <script src="https://cdn.jsdelivr.net/npm/chart.js"></script>
    <style>
        body { font-family: sans-serif; padding: 20px; background: #f4f4f9; color: #333; }
        .container { max-width: 800px; margin: 0 auto; background: white; padding: 20px; border-radius: 8px; box-shadow: 0 2px 10px rgba(0,0,0,0.1); }
        h1 { text-align: center; margin-top: 0; }
        
        .control-panel { 
            display: flex; gap: 15px; align-items: center; justify-content: center; 
            margin-bottom: 20px; padding: 15px; background: #eee; border-radius: 4px; 
        }
        input[type="text"] { padding: 8px; width: 200px; border: 1px solid #ccc; border-radius: 4px; }
        button { padding: 8px 16px; background: #007bff; color: white; border: none; border-radius: 4px; cursor: pointer; }
        button:hover { background: #0056b3; }
        
        /* Toggle Switch Styling */
        .toggle-container { display: flex; align-items: center; gap: 8px; font-weight: bold; }
        .switch { position: relative; display: inline-block; width: 40px; height: 24px; }
        .switch input { opacity: 0; width: 0; height: 0; }
        .slider { position: absolute; cursor: pointer; top: 0; left: 0; right: 0; bottom: 0; background-color: #ccc; transition: .4s; border-radius: 34px; }
        .slider:before { position: absolute; content: ""; height: 16px; width: 16px; left: 4px; bottom: 4px; background-color: white; transition: .4s; border-radius: 50%; }
        input:checked + .slider { background-color: #dc3545; } /* Red for danger/fail */
        input:checked + .slider:before { transform: translateX(16px); }

        .stats { display: flex; justify-content: space-around; margin-bottom: 20px; }
        .stat-box { text-align: center; }
        .stat-val { font-size: 1.5em; font-weight: bold; color: #007bff; }
        .error-val { color: #dc3545; }

        .terminal-container { margin-top: 20px; }
        .terminal-header { background: #333; color: white; padding: 5px 10px; border-radius: 4px 4px 0 0; font-size: 0.9em; }
        .terminal-window { 
            background: #1e1e1e; color: #00ff00; font-family: 'Courier New', monospace; 
            height: 150px; overflow-y: auto; padding: 10px; border-radius: 0 0 4px 4px; font-size: 0.85em;
            display: flex; flex-direction: column; 
        }
        .log-entry { margin-bottom: 2px; border-bottom: 1px solid #333; }
        .log-error { color: #ff4444; font-weight: bold; }
    </style>
</head>
<body>
    <div class="container">
        <h1>System Monitor</h1>

        <div class="control-panel">
            <div>
                <input type="text" id="payloadInput" value="Hello Board" placeholder="Enter payload text">
                <button onclick="updatePayload()">Update Payload</button>
            </div>
            
            <div class="toggle-container">
                <label class="switch">
                    <input type="checkbox" id="failToggle" onchange="toggleFail()">
                    <span class="slider"></span>
                </label>
                <span>Simulate Error</span>
            </div>
        </div>

        <div class="stats">
            <div class="stat-box">
                <div>RTT</div>
                <div id="rtt-display" class="stat-val">-- ms</div>
            </div>
            <div class="stat-box">
                <div>Echo Payload</div>
                <div id="payload-display" class="stat-val">-- bytes</div>
            </div>
            <div class="stat-box">
                <div>Packet Loss</div>
                <div id="loss-display" class="stat-val error-val">0%</div>
            </div>
        </div>

        <canvas id="liveChart"></canvas>

        <div class="terminal-container">
            <div class="terminal-header">Server Response Log</div>
            <div id="terminal-window" class="terminal-window"></div>
        </div>
    </div>

    <script>
        const ctx = document.getElementById('liveChart').getContext('2d');
        const termWindow = document.getElementById('terminal-window');
        let totalPings = 0;
        let failedPings = 0;

        const chart = new Chart(ctx, {
            type: 'line',
            data: {
                labels: [],
                datasets: [{
                    label: 'RTT (ms)',
                    data: [],
                    borderColor: '#007bff',
                    tension: 0.3,
                    fill: false
                }]
            },
            options: { scales: { y: { beginAtZero: true } }, animation: false }
        });

        const ws = new WebSocket("ws://" + location.host + "/ws");
        
        ws.onmessage = (event) => {
            const data = JSON.parse(event.data);
            totalPings++;

            // Handle Display Logic
            // We treat 'success=false' (network timeout) AND 'is_logical_error' (server sent "Connection failed") as errors
            const isError = !data.success || data.is_logical_error;

            if (isError) {
                if(!data.success) failedPings++; // Only count network timeouts as packet loss in %
                
                updateChart(null); // Break the line
                
                const rttText = document.getElementById('rtt-display');
                if (data.server_response === "Connection failed") {
                     rttText.innerText = "FAILED";
                } else {
                     rttText.innerText = "TIMEOUT";
                }
                rttText.style.color = "#dc3545";
                
                logToTerminal(data.server_response, true);
            } else {
                updateChart(data.rtt_ms);
                document.getElementById('rtt-display').innerText = data.rtt_ms.toFixed(1) + " ms";
                document.getElementById('rtt-display').style.color = "#007bff";
                logToTerminal(data.server_response, false);
            }

            document.getElementById('payload-display').innerText = data.payload_size + " bytes";
            const lossPct = (failedPings / totalPings * 100).toFixed(1);
            document.getElementById('loss-display').innerText = lossPct + "%";
        };

        function updateChart(rtt) {
            const now = new Date().toLocaleTimeString();
            chart.data.labels.push(now);
            chart.data.datasets[0].data.push(rtt);
            if (chart.data.labels.length > 20) {
                chart.data.labels.shift();
                chart.data.datasets[0].data.shift();
            }
            chart.update();
        }

        function logToTerminal(msg, isError) {
            const now = new Date().toLocaleTimeString();
            const div = document.createElement("div");
            div.className = "log-entry" + (isError ? " log-error" : "");
            div.innerText = `[${now}] ${msg}`;
            termWindow.appendChild(div);
            termWindow.scrollTop = termWindow.scrollHeight;
        }

        function updatePayload() {
            const text = document.getElementById('payloadInput').value;
            ws.send(JSON.stringify({ type: "UpdatePayload", value: text }));
        }

        function toggleFail() {
            const isChecked = document.getElementById('failToggle').checked;
            ws.send(JSON.stringify({ type: "ToggleFail", value: isChecked }));
        }
    </script>
</body>
</html>
"###;
