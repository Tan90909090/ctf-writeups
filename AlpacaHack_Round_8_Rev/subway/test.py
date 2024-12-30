#!/usr/bin/env python3

import math

LIST_COUNT = 32


# sub_2092
def float_is_plus(value: float) -> bool:
    assert value == 0.0 or value == -0.0
    return math.copysign(1, value) == 1.0


# sub_11A9
def float_not(value: float) -> float:
    assert value == 0.0 or value == -0.0
    return -value


# sub_11B1
# float_is_plus(float_logical_or(P, P)) = True
# float_is_plus(float_logical_or(P, M)) = True
# float_is_plus(float_logical_or(M, P)) = True
# float_is_plus(float_logical_or(M, M)) = False
def float_logical_or(v1: float, v2: float) -> float:
    assert v1 == 0.0 or v1 == -0.0
    assert v2 == 0.0 or v2 == -0.0
    return v1 - (-v2)


# sub_11D5
# float_is_plus(float_logical_and(P, P)) = True
# float_is_plus(float_logical_and(P, M)) = False
# float_is_plus(float_logical_and(M, P)) = False
# float_is_plus(float_logical_and(M, M)) = False
def float_logical_and(v1: float, v2: float) -> float:
    assert v1 == 0.0 or v1 == -0.0
    assert v2 == 0.0 or v2 == -0.0
    v1 = -v1
    v2 = -v2
    x = v1 - (-v2)
    return -x


# sub_120B
# float_is_plus(float_logical_xor_2(P, P)) = False
# float_is_plus(float_logical_xor_2(P, M)) = True
# float_is_plus(float_logical_xor_2(M, P)) = True
# float_is_plus(float_logical_xor_2(M, M)) = False
def float_logical_xor_2(v1: float, v2: float) -> float:
    assert v1 == 0.0 or v1 == -0.0
    assert v2 == 0.0 or v2 == -0.0

    v1_not = -v1
    f_and_a1not_a2 = float_logical_and(v1_not, v2)
    v2_not = -v2
    f_and_a1_a2not = float_logical_and(v1, v2_not)
    return float_logical_or(f_and_a1not_a2, f_and_a1_a2not)


def float_logical_xor_3(v1: float, v2: float, v3: float) -> float:
    assert v1 == 0.0 or v1 == -0.0
    assert v2 == 0.0 or v2 == -0.0
    assert v3 == 0.0 or v3 == -0.0
    return float_logical_xor_2(float_logical_xor_2(v1, v2), v3)


# sub_1279
# float_is_plus(float_at_least_2(P, P, P)) = True
# float_is_plus(float_at_least_2(P, P, M)) = True
# float_is_plus(float_at_least_2(P, M, P)) = True
# float_is_plus(float_at_least_2(P, M, M)) = False
# float_is_plus(float_at_least_2(M, P, P)) = True
# float_is_plus(float_at_least_2(M, P, M)) = False
# float_is_plus(float_at_least_2(M, M, P)) = False
# float_is_plus(float_at_least_2(M, M, M)) = False
def float_at_least_2(v1: float, v2: float, v3: float) -> float:
    assert v1 == 0.0 or v1 == -0.0
    assert v2 == 0.0 or v2 == -0.0
    assert v3 == 0.0 or v3 == -0.0

    f_or_12 = float_logical_and(v1, v2)
    f_or_13 = float_logical_and(v1, v3)
    f_or_23 = float_logical_and(v2, v3)
    return float_logical_or(float_logical_or(f_or_12, f_or_13), f_or_23)


def create_minus0_0x20_list() -> list[float]:
    return [-0.0] * LIST_COUNT


def create_float_array_bittest_32(value: int) -> list[float]:
    result = create_minus0_0x20_list()
    for i in range(LIST_COUNT):
        result[i] = 0.0 if ((value & (1 << i)) != 0) else -0.0
    return result


def float_array_slice(src: list[float], bit: int) -> list[float]:
    result = create_minus0_0x20_list()
    for i in range(1, 33):
        j = i - bit - 1
        if j >= 0:
            result[i - 1] = src[j]
    return result


# sub_14C2
def float_array_sum(src1: list[float], src2: list[float]) -> list[float]:
    result = create_minus0_0x20_list()
    current = -0.0
    for i in range(LIST_COUNT):
        result[i] = float_logical_xor_3(src1[i], src2[i], current)
        current = float_at_least_2(src1[i], src2[i], current)
    return result


# sub_1430
def float_array_sub(src1: list[float], src2: list[float]) -> list[float]:
    result = create_minus0_0x20_list()
    current = 0.0
    for i in range(LIST_COUNT):
        v2_not = float_not(src2[i])
        result[i] = float_logical_xor_3(src1[i], v2_not, current)
        current = float_at_least_2(src1[i], v2_not, current)
    return result


# sub_209C
def float_array_mul(src1: list[float], src2: list[float]) -> list[float]:
    result = create_minus0_0x20_list()
    for i in range(LIST_COUNT):
        if float_is_plus(src2[i]):
            sliced = float_array_slice(src1, i)
            result = float_array_sum(result, sliced)
    return result


def float_array_to_int(src: list[float]) -> int:
    value = 0
    for i in range(len(src)):
        b = float_is_plus(src[i])
        if b:
            value |= 1 << i
    return value


def dump_float_array(src: list[float]):
    value = 0
    for i in range(len(src)):
        b = float_is_plus(src[i])
        print(f"{i:02d} => {int(b)}")
        if b:
            value |= 1 << i
    print(f"{value = :#10x} ({value})")


P = 0.0
M = -0.0

assert float_is_plus((P)) is True
assert float_is_plus((M)) is False
assert float_is_plus(float_not(P)) is False
assert float_is_plus(float_not(M)) is True

print(f"{float_is_plus(float_logical_and(P, P)) = }")
print(f"{float_is_plus(float_logical_and(P, M)) = }")
print(f"{float_is_plus(float_logical_and(M, P)) = }")
print(f"{float_is_plus(float_logical_and(M, M)) = }")

print(f"{float_is_plus(float_at_least_2(P, P, P)) = }")
print(f"{float_is_plus(float_at_least_2(P, P, M)) = }")
print(f"{float_is_plus(float_at_least_2(P, M, P)) = }")
print(f"{float_is_plus(float_at_least_2(P, M, M)) = }")
print(f"{float_is_plus(float_at_least_2(M, P, P)) = }")
print(f"{float_is_plus(float_at_least_2(M, P, M)) = }")
print(f"{float_is_plus(float_at_least_2(M, M, P)) = }")
print(f"{float_is_plus(float_at_least_2(M, M, M)) = }")

for i in range(5):
    f_i = create_float_array_bittest_32(i)
    for j in range(5):
        f_j = create_float_array_bittest_32(j)
        f_result = float_array_sub(f_i, f_j)
        print(
            f"{float_array_to_int(f_i)} + {float_array_to_int(f_j)} => {float_array_to_int(f_result)}"
        )
