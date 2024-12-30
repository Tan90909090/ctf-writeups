#!/usr/bin/env python3
import math
import struct

import z3


def parse_expected_state() -> list[float]:
    # fmt:off
    data_3040 = bytes.fromhex("01 70 67 BF 2D 5A 10 BF 8B 91 2F BF 1C A5 02 3F AA 7C 0A 3F E9 E5 7D 3F 2A 47 13 BF 51 21 59 3F 2B EF 22 3F 23 37 BC BD 09 C2 1A BF 9E A7 3F 3F 8D 0D 5B BF 8F 23 B6 BE 98 92 2C 3F A7 D6 27 BF 24 3D 14 3F 46 DF 54 3F 86 F9 66 3E A2 06 1A BF 3B 7D A3 3E F3 3F 3A 3E F0 3D 16 3E 0D FC 44 BF 36 1B A9 3D C6 25 3A BF 05 A8 22 BE 6F 4D 1F 3F 77 4C 14 3F BC 4C BF BE 41 48 42 3F E2 0B 5F 3F 78 5A 73 BF 5D DB 78 BF EA 2F 67 BF 45 90 19 3F 98 06 24 BC AC 9B 78 3E 58 A4 A4 BE 30 84 29 3D D5 70 F0 3E AB EE 29 BE E0 67 08 BF 65 74 2D BF 69 FF E4 BE 0C 02 21 3F 39 42 D4 BE 1E 2A C3 3E A5 1C E1 BE 32 2B 8B BE 9B 28 44 BF F3 1E 89 3D 6C 82 A2 3E 46 0F A1 BE 83 3C 8F BE 79 40 5B 3F 49 1B 28 3F 3C 80 C9 BE CA 13 4B BF 5B 9B 01 BF 6E 7B 9E 3E 64 BF 14 BF 5B 04 0F 3F 3B 3A CE BE 7E BF 7E BE 85 55 71 BD 71 E2 2C BF B5 FE 72 BF 14 DD A8 BD 10 03 51 BF 21 FD FE 3C 91 CF 20 3F E9 76 4F BF CC F2 42 3F CF 60 40 BF 16 08 67 BF 77 43 51 BE B1 2D FC BD 06 54 0B 3F B7 22 E6 BD EC 38 20 BF D6 8A F0 BE 01 9F 7B BF 7C 86 0E BE 53 32 31 BF 1E 47 39 BE ED F4 08 BF EE 7E 2C BF 5A 48 2A 3F 91 37 44 BF 9B CF 5A BF 78 D4 89 BE 05 2B D4 BE 61 C3 48 BF 28 2F B5 3E EB 3F F0 3D 0C 5E 9F BE 5E E5 61 BF 47 E4 D7 3E D3 41 35 BE 59 99 06 BE 73 C9 88 3E 03 FE 5E 3F A2 8B 43 BF 11 F0 DD 3E 60 1B E0 BE F6 88 3A BF CA 68 6A 3F 3A 0A 38 BF 23 2B ED BD 80 9F 0E 3F 8A E4 C3 3D 7B 8E 73 3D 44 E1 05 BF 63 BB 65 BF 80 F3 69 3C A7 E6 93 BD D2 7A D5 BE 18 E9 2E 3F 1C 0C DA 3D 0E B1 C3 BE 5E A6 F2 3E BA 64 3B BF FB 2E D3 3E 7F 54 66 3E 79 C7 EB BE C7 08 7E BE 8A BC 93 3E 12 A9 7E BF 01 78 20 BF C1 7F 6E 3E 0A A1 08 BF FC 48 08 3E 2E BF 3C BE C4 4B 7B 3F 9C 32 3E 3E D6 9E 95 3E 8A E7 B8 BD 19 B9 32 3F C0 87 F4 BE AF 20 D0 3E 9E 12 72 BF 9A DD 27 3F FD 42 B7 BE DA 7E 1A 3F CA 07 38 3F ED 6B F2 3E 4B D5 5C 3E 99 EE 17 3E 2C 1A 6F BF 2A A9 38 3E DA C1 62 3F 72 E3 03 BF EE 02 2F 3E D9 A3 23 3F AE D4 66 BF 0F CB 79 BE 78 53 B8 3E 2D 05 18 3F 51 DC B8 BE D3 B8 54 BF 17 29 FA BE 78 36 4C 3F CD 26 01 3F 93 C4 F2 BE 62 5D 62 3F 70 DB 35 3F 2E DB 08 BF 40 E5 25 BF 0D EB 7D BF 61 0B 76 BF 4B 79 DB 3E 55 87 74 BF D4 9B 42 BE 9A C9 A3 3E C2 CB E5 3E 8D 51 30 3F 21 2B 80 3C 3D BC 30 BF BF 8D C5 3E 5A 58 A6 BC 1C 26 37 3F 70 C6 10 BE 77 F0 1B BF 60 09 CD 3E F9 E8 6A 3F 22 EA A0 3E FB A5 6A BF 0A 91 67 BF 5B 94 7E 3F 56 1F 4C 3F 89 41 B1 3E D8 AC DA 3E B5 5E 74 BE 90 DE 53 BF 48 E5 6E 3F 01 3F 8D 3E 5B F2 51 BE B1 91 97 3D B7 D0 FA BE 16 18 93 BC B0 A9 0D BF 5F 7C 31 BF 69 CB 37 BF 9A 19 CD 3E 34 EB 3C 3F 44 49 26 3F A3 54 4F 3E E8 D8 A2 3E 5C 7B A6 BE B7 D4 B4 BE 5D E0 64 3F EF 8D 22 3E B5 27 5D BF 12 F2 E0 BE 85 05 1E BF D1 09 D2 3E 61 D8 57 3F D5 CA 8E BD AA 19 0B 3E 7F 22 3D BE 57 4E D1 3E B5 23 B6 BE 2E 2B E7 BE 4A FB 2A 3F D6 12 12 BE 2F E1 9F 3C 36 F2 77 3F 4C C8 42 3F 7B 90 6F BF 86 DE B8 BE 63 FE 90 3E E6 17 09 BF A5 F1 12 3F FB 21 96 BE EB F2 3E BF 63 1B EC 3E 76 65 43 3F E1 6A A3 BE 5B 67 80 BC 87 37 7E 3F 0F 67 17 3F 8A C8 15 BE 6D CA 11 BF 99 F9 6A 3F F9 D1 D5 3E 4A 66 9B 3E 64 F3 E7 3D 52 2D BB 3B 19 F7 2F BF 1B BD 10 BF DA D7 0A 3F 39 43 B0 BE 3C 95 68 3F 55 0F BA BE B7 DB B5 BE AB E1 08 3F 74 11 51 BF 79 DE 89 3D 7E 6B 04 3F CD 7B 11 BF 16 86 A7 BC F7 7C 00 3F 7A 0A B6 BD 85 81 0C BF 75 34 EE BD 5F 63 96 3E C4 C1 25 3F 5D 2F 78 BF 99 C6 66 3F 15 87 32 3F B3 84 47 3E 6B 6B 17 BE 4F D9 42 BF 02 18 CD BE 39 58 1B 3F 28 AB 32 3F D0 C2 37 3F 0A B0 12 BF 04 4F 4A 3F 45 B2 26 3F AB 1A F7 3E 0A 2D 71 BF B6 FA B7 3E 3C 42 60 3F 5A 02 E0 BE A5 C4 55 3C FE ED 5C 3F D5 8F 5D BF 55 5A 44 BF 95 8F 53 BF 4E F0 B0 3E 03 70 2A BE AD 92 02 BF 9F 88 05 3F FD F3 AF BC 11 DE 6B BF 13 1F E2 BE 10 FE 88 BD EE E8 C4 BE D8 FF 0A 3F 25 F1 15 3F BF 4E AA 3E 1C FE 0F 3F 1F F2 01 BF 9A 0D 41 3D F1 6F 66 BF DD 95 8F 3E B0 11 4A BE 60 57 12 3D 7C CF 85 BE 9B DE A7 3E D6 12 49 3F E7 4A C9 BE FD 05 C7 BE 8E 9A 3E 3F 2C 5C 18 BF 63 C2 DA 3E 62 7A B8 BE 98 E2 13 3F E0 BF 7E 3F C6 A3 29 3F D2 CA 18 3F 1F BE F3 3E 8B 1D A1 3E A5 42 71 3F 1E CE 82 3D AC 2C 6B 3E 2C DD 38 3F 16 5E 67 3F 55 78 01 3F CA C7 25 3F 83 E4 39 3E 48 A9 0A 3F 5D A3 1F 3F 4A 2F 65 3F 4F E3 63 3F 31 25 5C BF AB 9F 7D 3F 22 6D 55 BF A0 A7 F1 BE 11 6C 29 BF 98 64 9A BE CC 48 49 BF EB F8 65 3F 4B 6E F1 3E 9D F8 91 3E 14 56 C8 BE 7C 52 38 BF B2 BD 14 3E 6F 82 EF 3E 43 CC 7E BF")
    # fmt:on
    assert len(data_3040) % 4 == 0
    result: list[float] = []
    for i in range(len(data_3040) // 4):
        t = struct.unpack("f", data_3040[i * 4 : (i + 1) * 4])
        # print(f"{t = }")
        result.append(t[0])

    return result


MOD = 0x1_0000_0000


def FloatArray_SumWithCarry(v1, v2):
    return (v1 + v2) % MOD


def FloatArray_SubWithBorrow(v1, v2):
    return (v1 - v2 + MOD) % MOD


# IDAの逆コンパイル結果を、parse.pyで加工した結果をそのまま貼り付けました
def convert_list_complexly(ppfloatArraySize11):
    ppfloatArraySize11[0] = ppfloatArraySize11[0]
    ppfloatArraySize11[1] = ppfloatArraySize11[1]
    ppfloatArraySize11[2] = ppfloatArraySize11[2]
    ppfloatArraySize11[3] = ppfloatArraySize11[3]
    ppfloatArraySize11[4] = ppfloatArraySize11[4]
    ppfloatArraySize11[5] = ppfloatArraySize11[5]
    ppfloatArraySize11[6] = ppfloatArraySize11[6]
    ppfloatArraySize11[7] = ppfloatArraySize11[7]
    ppfloatArraySize11[8] = ppfloatArraySize11[8]
    v3 = ppfloatArraySize11[9]
    ppfloatArraySize11[9] = v3
    v4 = ppfloatArraySize11[10]
    ppfloatArraySize11[10] = v4
    ppfloatArraySize11[9] = FloatArray_SubWithBorrow(v3, v4)
    ppfloatArraySize11[10] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[10], ppfloatArraySize11[5]
    )
    ppfloatArraySize11[9] = FloatArray_SumWithCarry(
        ppfloatArraySize11[9], ppfloatArraySize11[7]
    )
    ppfloatArraySize11[2] = FloatArray_SumWithCarry(
        ppfloatArraySize11[2], ppfloatArraySize11[4]
    )
    ppfloatArraySize11[1] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[1], ppfloatArraySize11[4]
    )
    ppfloatArraySize11[4] = FloatArray_SumWithCarry(
        ppfloatArraySize11[4], ppfloatArraySize11[0]
    )
    v5 = FloatArray_SumWithCarry(ppfloatArraySize11[0], ppfloatArraySize11[8])
    ppfloatArraySize11[0] = v5
    ppfloatArraySize11[4] = FloatArray_SubWithBorrow(ppfloatArraySize11[4], v5)
    v6 = FloatArray_SumWithCarry(ppfloatArraySize11[2], ppfloatArraySize11[0])
    ppfloatArraySize11[2] = v6
    ppfloatArraySize11[2] = FloatArray_SubWithBorrow(v6, ppfloatArraySize11[7])
    ppfloatArraySize11[9] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[9], ppfloatArraySize11[8]
    )
    v7 = FloatArray_SumWithCarry(ppfloatArraySize11[10], ppfloatArraySize11[6])
    ppfloatArraySize11[10] = v7
    ppfloatArraySize11[10] = FloatArray_SumWithCarry(v7, ppfloatArraySize11[9])
    ppfloatArraySize11[5] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[5], ppfloatArraySize11[6]
    )
    ppfloatArraySize11[1] = FloatArray_SumWithCarry(
        ppfloatArraySize11[1], ppfloatArraySize11[6]
    )
    ppfloatArraySize11[10] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[10], ppfloatArraySize11[5]
    )
    ppfloatArraySize11[3] = FloatArray_SumWithCarry(
        ppfloatArraySize11[3], ppfloatArraySize11[8]
    )
    ppfloatArraySize11[7] = FloatArray_SumWithCarry(
        ppfloatArraySize11[7], ppfloatArraySize11[1]
    )
    ppfloatArraySize11[1] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[1], ppfloatArraySize11[5]
    )
    ppfloatArraySize11[4] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[4], ppfloatArraySize11[2]
    )
    ppfloatArraySize11[10] = FloatArray_SumWithCarry(
        ppfloatArraySize11[10], ppfloatArraySize11[0]
    )
    ppfloatArraySize11[5] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[5], ppfloatArraySize11[8]
    )
    ppfloatArraySize11[10] = FloatArray_SumWithCarry(
        ppfloatArraySize11[10], ppfloatArraySize11[6]
    )
    ppfloatArraySize11[9] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[9], ppfloatArraySize11[5]
    )
    v8 = FloatArray_SubWithBorrow(ppfloatArraySize11[3], ppfloatArraySize11[7])
    ppfloatArraySize11[3] = v8
    ppfloatArraySize11[3] = FloatArray_SumWithCarry(v8, ppfloatArraySize11[6])
    v9 = FloatArray_SumWithCarry(ppfloatArraySize11[1], ppfloatArraySize11[7])
    ppfloatArraySize11[1] = v9
    ppfloatArraySize11[1] = FloatArray_SumWithCarry(v9, ppfloatArraySize11[9])
    ppfloatArraySize11[3] = FloatArray_SumWithCarry(
        ppfloatArraySize11[3], ppfloatArraySize11[5]
    )
    ppfloatArraySize11[4] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[4], ppfloatArraySize11[6]
    )
    ppfloatArraySize11[7] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[7], ppfloatArraySize11[1]
    )
    ppfloatArraySize11[10] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[10], ppfloatArraySize11[6]
    )
    ppfloatArraySize11[9] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[9], ppfloatArraySize11[8]
    )
    ppfloatArraySize11[1] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[1], ppfloatArraySize11[8]
    )
    ppfloatArraySize11[3] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[3], ppfloatArraySize11[0]
    )
    ppfloatArraySize11[0] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[0], ppfloatArraySize11[8]
    )
    ppfloatArraySize11[4] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[4], ppfloatArraySize11[8]
    )
    v10 = FloatArray_SumWithCarry(ppfloatArraySize11[9], ppfloatArraySize11[7])
    ppfloatArraySize11[9] = v10
    ppfloatArraySize11[9] = FloatArray_SumWithCarry(v10, ppfloatArraySize11[5])
    ppfloatArraySize11[0] = FloatArray_SumWithCarry(
        ppfloatArraySize11[0], ppfloatArraySize11[5]
    )
    ppfloatArraySize11[8] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[8], ppfloatArraySize11[5]
    )
    ppfloatArraySize11[5] = FloatArray_SumWithCarry(
        ppfloatArraySize11[5], ppfloatArraySize11[6]
    )
    v11 = FloatArray_SumWithCarry(ppfloatArraySize11[0], ppfloatArraySize11[6])
    ppfloatArraySize11[0] = v11
    ppfloatArraySize11[0] = FloatArray_SubWithBorrow(v11, ppfloatArraySize11[6])
    ppfloatArraySize11[4] = FloatArray_SumWithCarry(
        ppfloatArraySize11[4], ppfloatArraySize11[9]
    )
    ppfloatArraySize11[8] = FloatArray_SumWithCarry(
        ppfloatArraySize11[8], ppfloatArraySize11[10]
    )
    ppfloatArraySize11[6] = FloatArray_SumWithCarry(
        ppfloatArraySize11[6], ppfloatArraySize11[5]
    )
    ppfloatArraySize11[0] = FloatArray_SumWithCarry(
        ppfloatArraySize11[0], ppfloatArraySize11[7]
    )
    ppfloatArraySize11[8] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[8], ppfloatArraySize11[3]
    )
    ppfloatArraySize11[0] = FloatArray_SumWithCarry(
        ppfloatArraySize11[0], ppfloatArraySize11[2]
    )
    ppfloatArraySize11[4] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[4], ppfloatArraySize11[1]
    )
    ppfloatArraySize11[7] = FloatArray_SumWithCarry(
        ppfloatArraySize11[7], ppfloatArraySize11[1]
    )
    v12 = FloatArray_SumWithCarry(ppfloatArraySize11[4], ppfloatArraySize11[3])
    ppfloatArraySize11[4] = v12
    ppfloatArraySize11[8] = FloatArray_SumWithCarry(ppfloatArraySize11[8], v12)
    ppfloatArraySize11[7] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[7], ppfloatArraySize11[5]
    )
    ppfloatArraySize11[8] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[8], ppfloatArraySize11[3]
    )
    ppfloatArraySize11[9] = FloatArray_SumWithCarry(
        ppfloatArraySize11[9], ppfloatArraySize11[4]
    )
    ppfloatArraySize11[4] = FloatArray_SumWithCarry(
        ppfloatArraySize11[4], ppfloatArraySize11[0]
    )
    ppfloatArraySize11[8] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[8], ppfloatArraySize11[9]
    )
    ppfloatArraySize11[1] = FloatArray_SumWithCarry(
        ppfloatArraySize11[1], ppfloatArraySize11[9]
    )
    ppfloatArraySize11[5] = FloatArray_SumWithCarry(
        ppfloatArraySize11[5], ppfloatArraySize11[3]
    )
    ppfloatArraySize11[4] = FloatArray_SumWithCarry(
        ppfloatArraySize11[4], ppfloatArraySize11[8]
    )
    ppfloatArraySize11[7] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[7], ppfloatArraySize11[9]
    )
    ppfloatArraySize11[8] = FloatArray_SumWithCarry(
        ppfloatArraySize11[8], ppfloatArraySize11[1]
    )
    ppfloatArraySize11[10] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[10], ppfloatArraySize11[6]
    )
    ppfloatArraySize11[0] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[0], ppfloatArraySize11[3]
    )
    ppfloatArraySize11[3] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[3], ppfloatArraySize11[6]
    )
    ppfloatArraySize11[0] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[0], ppfloatArraySize11[5]
    )
    ppfloatArraySize11[10] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[10], ppfloatArraySize11[4]
    )
    ppfloatArraySize11[7] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[7], ppfloatArraySize11[8]
    )
    ppfloatArraySize11[10] = FloatArray_SumWithCarry(
        ppfloatArraySize11[10], ppfloatArraySize11[6]
    )
    ppfloatArraySize11[1] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[1], ppfloatArraySize11[6]
    )
    ppfloatArraySize11[4] = FloatArray_SumWithCarry(
        ppfloatArraySize11[4], ppfloatArraySize11[2]
    )
    ppfloatArraySize11[7] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[7], ppfloatArraySize11[3]
    )
    ppfloatArraySize11[4] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[4], ppfloatArraySize11[6]
    )
    ppfloatArraySize11[6] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[6], ppfloatArraySize11[5]
    )
    ppfloatArraySize11[2] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[2], ppfloatArraySize11[3]
    )
    ppfloatArraySize11[4] = FloatArray_SumWithCarry(
        ppfloatArraySize11[4], ppfloatArraySize11[6]
    )
    ppfloatArraySize11[9] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[9], ppfloatArraySize11[7]
    )
    ppfloatArraySize11[8] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[8], ppfloatArraySize11[3]
    )
    ppfloatArraySize11[5] = FloatArray_SumWithCarry(
        ppfloatArraySize11[5], ppfloatArraySize11[0]
    )
    ppfloatArraySize11[9] = FloatArray_SumWithCarry(
        ppfloatArraySize11[9], ppfloatArraySize11[1]
    )
    ppfloatArraySize11[4] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[4], ppfloatArraySize11[10]
    )
    ppfloatArraySize11[0] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[0], ppfloatArraySize11[3]
    )
    v13 = FloatArray_SumWithCarry(ppfloatArraySize11[2], ppfloatArraySize11[6])
    ppfloatArraySize11[2] = v13
    ppfloatArraySize11[2] = FloatArray_SumWithCarry(v13, ppfloatArraySize11[4])
    ppfloatArraySize11[3] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[3], ppfloatArraySize11[0]
    )
    ppfloatArraySize11[2] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[2], ppfloatArraySize11[9]
    )
    ppfloatArraySize11[0] = FloatArray_SumWithCarry(
        ppfloatArraySize11[0], ppfloatArraySize11[8]
    )
    v14 = FloatArray_SubWithBorrow(ppfloatArraySize11[9], ppfloatArraySize11[6])
    ppfloatArraySize11[9] = v14
    ppfloatArraySize11[9] = FloatArray_SubWithBorrow(v14, ppfloatArraySize11[2])
    ppfloatArraySize11[5] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[5], ppfloatArraySize11[6]
    )
    v15 = FloatArray_SumWithCarry(ppfloatArraySize11[0], ppfloatArraySize11[2])
    ppfloatArraySize11[0] = v15
    ppfloatArraySize11[3] = FloatArray_SubWithBorrow(ppfloatArraySize11[3], v15)
    v16 = FloatArray_SumWithCarry(ppfloatArraySize11[7], ppfloatArraySize11[4])
    ppfloatArraySize11[7] = v16
    ppfloatArraySize11[0] = FloatArray_SumWithCarry(ppfloatArraySize11[0], v16)
    ppfloatArraySize11[3] = FloatArray_SumWithCarry(
        ppfloatArraySize11[3], ppfloatArraySize11[4]
    )
    ppfloatArraySize11[5] = FloatArray_SumWithCarry(
        ppfloatArraySize11[5], ppfloatArraySize11[10]
    )
    ppfloatArraySize11[10] = FloatArray_SumWithCarry(
        ppfloatArraySize11[10], ppfloatArraySize11[0]
    )
    ppfloatArraySize11[1] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[1], ppfloatArraySize11[3]
    )
    v17 = FloatArray_SubWithBorrow(ppfloatArraySize11[2], ppfloatArraySize11[3])
    ppfloatArraySize11[2] = v17
    ppfloatArraySize11[2] = FloatArray_SumWithCarry(v17, ppfloatArraySize11[4])
    v18 = FloatArray_SubWithBorrow(ppfloatArraySize11[0], ppfloatArraySize11[9])
    ppfloatArraySize11[0] = v18
    ppfloatArraySize11[0] = FloatArray_SubWithBorrow(v18, ppfloatArraySize11[4])
    ppfloatArraySize11[10] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[10], ppfloatArraySize11[4]
    )
    ppfloatArraySize11[6] = FloatArray_SumWithCarry(
        ppfloatArraySize11[6], ppfloatArraySize11[0]
    )
    v19 = FloatArray_SumWithCarry(ppfloatArraySize11[4], ppfloatArraySize11[3])
    ppfloatArraySize11[4] = v19
    ppfloatArraySize11[8] = FloatArray_SubWithBorrow(ppfloatArraySize11[8], v19)
    ppfloatArraySize11[1] = FloatArray_SumWithCarry(
        ppfloatArraySize11[1], ppfloatArraySize11[0]
    )
    ppfloatArraySize11[9] = FloatArray_SumWithCarry(
        ppfloatArraySize11[9], ppfloatArraySize11[6]
    )
    ppfloatArraySize11[3] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[3], ppfloatArraySize11[2]
    )
    ppfloatArraySize11[9] = FloatArray_SumWithCarry(
        ppfloatArraySize11[9], ppfloatArraySize11[2]
    )
    ppfloatArraySize11[2] = FloatArray_SumWithCarry(
        ppfloatArraySize11[2], ppfloatArraySize11[5]
    )
    ppfloatArraySize11[8] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[8], ppfloatArraySize11[5]
    )
    ppfloatArraySize11[0] = FloatArray_SumWithCarry(
        ppfloatArraySize11[0], ppfloatArraySize11[9]
    )
    ppfloatArraySize11[6] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[6], ppfloatArraySize11[5]
    )
    ppfloatArraySize11[1] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[1], ppfloatArraySize11[9]
    )
    ppfloatArraySize11[5] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[5], ppfloatArraySize11[7]
    )
    ppfloatArraySize11[4] = FloatArray_SumWithCarry(
        ppfloatArraySize11[4], ppfloatArraySize11[7]
    )
    ppfloatArraySize11[7] = FloatArray_SumWithCarry(
        ppfloatArraySize11[7], ppfloatArraySize11[2]
    )
    ppfloatArraySize11[8] = FloatArray_SumWithCarry(
        ppfloatArraySize11[8], ppfloatArraySize11[0]
    )
    ppfloatArraySize11[0] = FloatArray_SumWithCarry(
        ppfloatArraySize11[0], ppfloatArraySize11[4]
    )
    v20 = FloatArray_SumWithCarry(ppfloatArraySize11[5], ppfloatArraySize11[1])
    ppfloatArraySize11[5] = v20
    ppfloatArraySize11[5] = FloatArray_SumWithCarry(v20, ppfloatArraySize11[6])
    v21 = FloatArray_SumWithCarry(ppfloatArraySize11[4], ppfloatArraySize11[8])
    ppfloatArraySize11[4] = v21
    v22 = FloatArray_SumWithCarry(ppfloatArraySize11[0], v21)
    ppfloatArraySize11[0] = v22
    ppfloatArraySize11[6] = FloatArray_SumWithCarry(ppfloatArraySize11[6], v22)
    ppfloatArraySize11[0] = FloatArray_SumWithCarry(
        ppfloatArraySize11[0], ppfloatArraySize11[7]
    )
    v23 = FloatArray_SumWithCarry(ppfloatArraySize11[4], ppfloatArraySize11[9])
    ppfloatArraySize11[4] = v23
    ppfloatArraySize11[4] = FloatArray_SubWithBorrow(v23, ppfloatArraySize11[7])
    ppfloatArraySize11[9] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[9], ppfloatArraySize11[2]
    )
    ppfloatArraySize11[0] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[0], ppfloatArraySize11[3]
    )
    ppfloatArraySize11[10] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[10], ppfloatArraySize11[5]
    )
    ppfloatArraySize11[0] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[0], ppfloatArraySize11[4]
    )
    ppfloatArraySize11[7] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[7], ppfloatArraySize11[1]
    )
    v24 = FloatArray_SumWithCarry(ppfloatArraySize11[3], ppfloatArraySize11[0])
    ppfloatArraySize11[3] = v24
    v25 = FloatArray_SumWithCarry(v24, ppfloatArraySize11[6])
    ppfloatArraySize11[3] = v25
    ppfloatArraySize11[3] = FloatArray_SumWithCarry(v25, ppfloatArraySize11[4])
    ppfloatArraySize11[6] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[6], ppfloatArraySize11[10]
    )
    v26 = FloatArray_SubWithBorrow(ppfloatArraySize11[3], ppfloatArraySize11[7])
    ppfloatArraySize11[3] = v26
    ppfloatArraySize11[3] = FloatArray_SumWithCarry(v26, ppfloatArraySize11[0])
    ppfloatArraySize11[8] = FloatArray_SumWithCarry(
        ppfloatArraySize11[8], ppfloatArraySize11[7]
    )
    ppfloatArraySize11[4] = FloatArray_SumWithCarry(
        ppfloatArraySize11[4], ppfloatArraySize11[0]
    )
    ppfloatArraySize11[8] = FloatArray_SumWithCarry(
        ppfloatArraySize11[8], ppfloatArraySize11[3]
    )
    ppfloatArraySize11[4] = FloatArray_SumWithCarry(
        ppfloatArraySize11[4], ppfloatArraySize11[6]
    )
    ppfloatArraySize11[1] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[1], ppfloatArraySize11[0]
    )
    ppfloatArraySize11[2] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[2], ppfloatArraySize11[9]
    )
    ppfloatArraySize11[7] = FloatArray_SumWithCarry(
        ppfloatArraySize11[7], ppfloatArraySize11[8]
    )
    ppfloatArraySize11[1] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[1], ppfloatArraySize11[8]
    )
    ppfloatArraySize11[4] = FloatArray_SubWithBorrow(
        ppfloatArraySize11[4], ppfloatArraySize11[8]
    )


UNIT = 32


# sub_21B1で正解扱いとなる、sub_167Aの入力を返します。
def inv_21B1_167A():
    EXPECTED_STATE = parse_expected_state()
    solver = z3.Solver()
    bit_values_bitvec = [z3.BitVec(f"value_{i:02d}", 32) for i in range(11)]
    bit_values_bitvec_copied = bit_values_bitvec[::]
    convert_list_complexly(bit_values_bitvec_copied)

    assert len(EXPECTED_STATE) == 11 * 32
    for i in range(len(EXPECTED_STATE)):
        if math.copysign(1, EXPECTED_STATE[i]) > 0:
            solver.add(((bit_values_bitvec_copied[i // UNIT] >> (i % UNIT)) & 1) == 1)
        else:
            solver.add(((bit_values_bitvec_copied[i // UNIT] >> (i % UNIT)) & 1) == 0)

    if solver.check() != z3.sat:
        raise Exception("Can not solve...")
    model = solver.model()
    result = [model[bitvec].as_long() for bitvec in bit_values_bitvec]  # type:ignore

    # 別解がないことを確認
    block = []
    for i in range(len(bit_values_bitvec)):
        block.append(bit_values_bitvec[i] != result[i])
    solver.add(z3.Or(block))
    assert solver.check() != z3.sat

    return result


# あとはsub_20FEとsub_159Dの逆演算でフラグを復元できます
bit_values_concrete = inv_21B1_167A()
# print(bit_values_concrete)
# print(f"{len(bit_values_concrete) = }")
assert len(bit_values_concrete) == 11

for i in range(len(bit_values_concrete)):
    v = 0
    for j in range(UNIT):
        tmp = (bit_values_concrete[i] >> j) & 1
        assert tmp == 0 or tmp == 1
        v |= tmp << j

    v ^= 2238381247
    inv_34974707 = pow(34974707, -1, MOD)
    v = (v * inv_34974707) % MOD

    print(v.to_bytes(4, "little").decode(), end="")
print()
