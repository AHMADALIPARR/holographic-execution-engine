#!/usr/bin/env python3
# HP-OTR: Holographic Polymorphism OmniTime Recursion
# Copyright (C) 2026 AHMAD ALI PARR / SnapKitty Research Lab
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU Affero General Public License as published
# by the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
# GNU Affero General Public License for more details.
#
# You should have received a copy of the GNU Affero General Public License
# along with this program. If not, see <https://www.gnu.org/licenses/>.
from __future__ import annotations
import numpy as np
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import List, Tuple

# ---------------------------------------------------------------------------
# Core types
# ---------------------------------------------------------------------------

class TypeSig(Enum):
    SCALAR = auto()
    VECTOR = auto()
    MATRIX = auto()
    TENSOR = auto()

    def bond_dim(self, base: int = 2) -> int:
        if self is TypeSig.SCALAR:
            return 1
        if self is TypeSig.VECTOR:
            return base
        if self is TypeSig.MATRIX:
            return base * base
        if self is TypeSig.TENSOR:
            return base * base * base
        return 1

    @staticmethod
    def from_curvature(c: float, base: int = 2) -> "TypeSig":
        if c > 1.5:
            return TypeSig.TENSOR
        if c > 0.5:
            return TypeSig.MATRIX
        if c > -0.5:
            return TypeSig.VECTOR
        return TypeSig.SCALAR


@dataclass
class BulkGeometry:
    curvature: float = 0.0
    ads_radius: float = 1.0
    gn: float = 1.0
    dimension: int = 3
    tau: Tuple[float, float] = (0.0, 0.0)

    def project_to_boundary(self) -> TypeSig:
        return TypeSig.from_curvature(self.curvature, base=2)

    def rt_area(self, k: int, k_prime: int, depth: int) -> float:
        dk = abs(k - k_prime) / max(depth, 1)
        base = (self.ads_radius ** (self.dimension - 1)) / (4.0 * ++[self.gn](http://self.gn/)++)
        return base * (1.0 + abs(self.curvature)) * np.log1p(1.0 + dk)

    def geodesic_length(self, k: int, k_prime: int, depth: int) -> float:
        dk = abs(k - k_prime) / max(depth, 1)
        arg = 1.0 + dk
        return self.ads_radius * np.log(arg) * (1.0 + 0.1 * abs(self.curvature))


# ---------------------------------------------------------------------------
# Holographic Wiring Function π(σ, τ)
# ---------------------------------------------------------------------------

def holographic_wiring(
    bulk: BulkGeometry,
    sigma: List[TypeSig],
    depth: int,
    source: int,
) -> List[Tuple[int, float]]:
    weights: List[Tuple[int, float]] = []
    s0 = 1.0
    l0 = max(bulk.ads_radius, 1e-8)

    for k_prime in range(depth):
        if k_prime == source:
            continue
        area = bulk.rt_area(source, k_prime, depth)
        s_rt = area / (4.0 * ++[bulk.gn](http://bulk.gn/)++)
        ell = bulk.geodesic_length(source, k_prime, depth)

        w_geom = np.exp(-ell / l0) * np.exp(s_rt / s0)

        chi_s = sigma[source].bond_dim()
        chi_t = sigma[k_prime].bond_dim()
        f = 1.0 if chi_s == chi_t else min(chi_s, chi_t) / max(chi_s, chi_t, 1)

        weight = float(w_geom * f)
        weights.append((k_prime, weight))

    weights.sort(key=lambda x: x[1], reverse=True)
    return weights


def select_targets(
    bulk: BulkGeometry,
    sigma: List[TypeSig],
    depth: int,
    source: int,
    m: int,
) -> List[int]:
    ranked = holographic_wiring(bulk, sigma, depth, source)
    return [k for k, _ in ranked[:m]]


# ---------------------------------------------------------------------------
# Polymorphic Embedding
# ---------------------------------------------------------------------------

def embedding_operator(chi_in: int, chi_out: int) -> np.ndarray:
    u = np.zeros((chi_out, chi_in), dtype=np.complex128)
    n = min(chi_in, chi_out)
    for i in range(n):
        u[i, i] = 1.0 + 0.0j
    return u


# ---------------------------------------------------------------------------
# ER-Bridge
# ---------------------------------------------------------------------------

@dataclass
class ERBridge:
    depth: int
    max_bond: int

    def contract_multi(
        self,
        memory: np.ndarray,
        bulk: BulkGeometry,
        sigma: List[TypeSig],
        source: int,
        m_targets: int,
    ) -> None:
        chi_s = min(sigma[source].bond_dim(), self.max_bond)
        targets = select_targets(bulk, sigma, self.depth, source, m_targets)

        src_block = memory[source, :chi_s, :chi_s].copy()

        for tgt in targets:
            chi_t = min(sigma[tgt].bond_dim(), self.max_bond)
            u = embedding_operator(chi_s, chi_t)
            # ρ_t = U ρ_s U†
            tmp = u @ src_block
            rho_t = tmp @ u.conj().T
            memory[tgt, :chi_t, :chi_t] = rho_t

        # Source back-reaction (decoherence)
        factor = 1.0 / np.sqrt(len(targets) + 1)
        memory[source, :chi_s, :chi_s] = src_block * factor

        # Update types
        new_type = bulk.project_to_boundary()
        for tgt in targets:
            sigma[tgt] = new_type


# ---------------------------------------------------------------------------
# HP-OTR model
# ---------------------------------------------------------------------------

@dataclass
class HpotR:
    depth: int
    max_bond: int
    bulk: BulkGeometry = field(default_factory=lambda: BulkGeometry(0.8))
    memory: np.ndarray = field(init=False)
    sigma: List[TypeSig] = field(init=False)
    bridge: ERBridge = field(init=False)

    def __post_init__(self) -> None:
        self.memory = np.zeros((self.depth, self.max_bond, self.max_bond), dtype=np.complex128)
        n = min(self.max_bond, 4)
        for k in range(self.depth):
            for i in range(n):
                self.memory[k, i, i] = 1.0 / n + 0.0j

        self.sigma = [self.bulk.project_to_boundary() for _ in range(self.depth)]
        self.bridge = ERBridge(self.depth, self.max_bond)

    def step(self, source: int, m_targets: int) -> None:
        self.sigma[source] = self.bulk.project_to_boundary()
        self.bridge.contract_multi(
            self.memory, self.bulk, self.sigma, source, m_targets
        )

        chi = min(self.sigma[source].bond_dim(), self.max_bond)
        block = self.memory[source, :chi, :chi]
        purity = float(np.sum(np.abs(block) ** 2))
        entropy_approx = -np.log(purity + 1e-12)
        self.bulk.curvature += 0.01 * entropy_approx

        tr, ti = self.bulk.tau
        self.bulk.tau = (tr + 0.1, ti + 1.0)

    def run(self, steps: int, m_targets: int) -> None:
        for t in range(steps):
            source = t % self.depth
            self.step(source, m_targets)

    def total_entropy(self) -> float:
        s = 0.0
        for k in range(self.depth):
            chi = min(self.sigma[k].bond_dim(), self.max_bond)
            block = self.memory[k, :chi, :chi]
            p = float(np.sum(np.abs(block) ** 2))
            s += -np.log(p + 1e-15)
        return s


# ---------------------------------------------------------------------------
# Main demo
# ---------------------------------------------------------------------------

def main() -> None:
    depth = 32
    max_bond = 8
    model = HpotR(depth=depth, max_bond=max_bond)

    print("=== HP-OTR Runnable Demo ===")
    print(f"Depth : {depth}")
    print(f"Max bond dim : {max_bond}")
    print(f"Initial entropy proxy : {model.total_entropy():.6f}")
    print(f"Initial type at k=0 : {model.sigma[0].name}")
    print(f"Initial curvature : {model.bulk.curvature:.6f}")

    steps = 100
    m_targets = 3
    print(f"\nRunning {steps} OmniTime steps ({m_targets} targets each)...")
    model.run(steps, m_targets)

    print("\n=== After evolution ===")
    print(f"Final entropy proxy : {model.total_entropy():.6f}")
    print(f"Final curvature : {model.bulk.curvature:.6f}")
    print(f"Final type at k=0 : {model.sigma[0].name}")
    print(f"OmniTime (τ_r, τ_i) : ({model.bulk.tau[0]:.2f}, {model.bulk.tau[1]:.2f})")

    wiring = holographic_wiring(model.bulk, model.sigma, depth, 5)
    print("\nTop-5 holographic wirings from source k=5:")
    for i, (tgt, w) in enumerate(wiring[:5]):
        print(f" #{i+1:<2} → k={tgt:<3} weight={w:.6f}")

    print("\nDone.")


if __name__ == "__main__":
    main()
