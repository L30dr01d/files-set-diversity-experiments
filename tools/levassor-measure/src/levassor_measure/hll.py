from __future__ import annotations

import math

_MASK64 = (1 << 64) - 1


class HyperLogLog:
    def __init__(self, p: int = 14) -> None:
        self.p = p
        self.m = 1 << p
        self.registers = [0] * self.m
        self._alpha = 0.7213 / (1.0 + 1.079 / self.m)

    def add(self, value: int) -> None:
        hashed = value & _MASK64
        index = hashed >> (64 - self.p)
        rest = hashed & ((1 << (64 - self.p)) - 1)
        width = 64 - self.p
        if rest == 0:
            leading = width
        else:
            leading = width - rest.bit_length()
        rank = 1 + leading
        if rank > self.registers[index]:
            self.registers[index] = rank

    def cardinality(self) -> float:
        if all(register == 0 for register in self.registers):
            return 0.0
        harmonic = sum(2.0 ** (-register) for register in self.registers)
        raw = self._alpha * (self.m ** 2) / harmonic
        zeros = sum(1 for register in self.registers if register == 0)
        if raw <= 2.5 * self.m and zeros > 0:
            return float(self.m * math.log(self.m / zeros))
        return float(raw)
