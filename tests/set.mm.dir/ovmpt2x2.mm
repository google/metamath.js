include "wcel.mm"
include "w3a.mm"
include "cmpt2.mm"
include "wceq.mm"
include "a1i.mm"
include "cv.mm"
include "wa.mm"
include "adantl.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "ovmpt2rdx.mm"

theorem ovmpt2x2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cF: class F
  let cH: class H
  let cL: class L
  let vk: setvar k
  assume ovmpt2x2.1: |- ( ( x = A /\ y = B ) -> R = S )
  assume ovmpt2x2.2: |- ( y = B -> C = L )
  assume ovmpt2x2.3: |- F = ( x e. C , y e. D |-> R )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint D x
  disjoint D y
  disjoint H x
  disjoint H y
  disjoint L x
  disjoint L y
  disjoint S x
  disjoint S y
  disjoint k x
  assert |- ( ( A e. L /\ B e. D /\ S e. H ) -> ( A F B ) = S )

  proof
    cA
    cL
    wcel
    #
    cB
    cD
    wcel
    #
    cS
    cH
    wcel
    #
    w3a
    #
    vx
    vy
    cA
    cB
    cC
    cD
    cR
    cS
    cF
    cL
    cH
    cF
    vx
    vy
    cC
    cD
    cR
    cmpt2
    wceq
    @3
    ovmpt2x2.3
    a1i
    vx
    cv
    cA
    wceq
    vy
    cv
    cB
    wceq
    #
    wa
    cR
    cS
    wceq
    @3
    ovmpt2x2.1
    adantl
    @4
    cC
    cL
    wceq
    @3
    ovmpt2x2.2
    adantl
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    ovmpt2rdx
end
