#!/usr/bin/env python3

import pwn
import z3

MOD = 0x1_0000_0000


def byte_array_to_dword_array(a: bytes) -> list[int]:
    assert len(a) % 4 == 0

    result: list[int] = []
    for i in range(len(a) // 4):
        v: int = pwn.u32(a[i * 4 : (i + 1) * 4])
        result.append(v)
    return result


def RotateLeft32(value: int, bit: int) -> int:
    assert 0 <= bit < 32
    assert 0 <= value < MOD
    return ((value << bit) | (value >> (32 - bit))) % MOD


def RotateRight32(value: int, bit: int) -> int:
    assert 0 <= bit < 32
    assert 0 <= value < MOD
    return ((value >> bit) | (value << (32 - bit))) % MOD


def convert(
    part: int | z3.BitVecRef, work: list[int]
) -> tuple[int, int, int | z3.BitVecRef]:
    value1 = (RotateLeft32(work[0], 5) + RotateRight32(work[1], 3)) % MOD
    value2 = (RotateRight32(work[2], 3) - RotateLeft32(work[3], 5) + MOD) % MOD
    value3 = (part ^ value1 ^ value2) % MOD
    # ここでvalue3で分岐してしまうと、シンボリック変数のままだからか思った分岐になりませんでした。後で判断します
    # 教訓: 「(value3 & 1) != 0」等で「Symbolic expressions cannot be cast to concrete Boolean values.」が出るときは本当に間違っています。
    return (value1, value2, value3)


# fmt:off
# 4040からShift+EでExport data
expected_bytes = bytes.fromhex("DC 86 1A 9A DD 93 9B 35 D3 74 DA EE E8 5A 3C C5 1C 64 33 47 D2 3B 28 F3 CC 5A 48 8B 74 0C 4B 87 38 D6 80 40 51 E6 4A 27 A1 73 52 0F 93 06 54 3D 65 13 FB C8 65 AF D2 67 B3 09 EF 7D 23 A6 76 E5 13 10 13 FF 34 8D AE D0 9C 2C 4D F3 A1 BC 46 2F 98 87 B6 57 1A A2 17 F1 F0 E5 B0 BA 9B 6D B5 A7 AC 6A 5E AC E8 F6 90 D8 B0 A2 99 91")
expected_dwords = byte_array_to_dword_array(expected_bytes)
assert len(expected_dwords) == 27
# fmt:on

work: list[int] = byte_array_to_dword_array(b"AlpacaHackRound8")

solver = z3.Solver()
flag_input = [z3.BitVec(f"flag_{i:02d}", 8) for i in range(4 * 27)]

for i in range(len(flag_input) // 4):
    value_input = (
        (z3.ZeroExt(32, flag_input[(4 * i) + 0]) << 0)
        | (z3.ZeroExt(32, flag_input[(4 * i) + 1]) << 8)
        | (z3.ZeroExt(32, flag_input[(4 * i) + 2]) << 16)
        | (z3.ZeroExt(32, flag_input[(4 * i) + 3]) << 24)
    )
    (value1_concret, value2_concret, value3_symbolic) = convert(value_input, work)
    solver.add(value3_symbolic == expected_dwords[i])

    if solver.check() != z3.sat:
        raise Exception("Can not solve...")

    # なるはずの値は分かっているので、簡単のためそちらを使います
    value3_concrete = expected_dwords[i]

    if (value3_concrete & 1) == 1:
        work[0] ^= RotateLeft32(value2_concret, 11)
        work[1] ^= RotateLeft32(value2_concret, 13)
        work[2] ^= RotateRight32(value1_concret, 15)
        work[3] ^= RotateRight32(value1_concret, 13)
    else:
        work[0] ^= RotateRight32(value2_concret, 13)
        work[1] ^= RotateRight32(value2_concret, 15)
        work[2] ^= RotateLeft32(value1_concret, 13)
        work[3] ^= RotateLeft32(value1_concret, 11)

flag_result = ""
model = solver.model()
for f in flag_input:
    flag_result += chr(model[f].as_long())  # type:ignore
print(flag_result.strip("\x00"))
