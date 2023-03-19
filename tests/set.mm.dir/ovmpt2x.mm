include "wcel.mm"
include "cvv.mm"
include "co.mm"
include "wceq.mm"
include "elex.mm"
include "w3a.mm"
include "cmpt2.mm"
include "a1i.mm"
include "cv.mm"
include "wa.mm"
include "adantl.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "ovmpt2dx.mm"
include "syl3an3.mm"

theorem ovmpt2x
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
  assume ovmpt2x.1: |- ( ( x = A /\ y = B ) -> R = S )
  assume ovmpt2x.2: |- ( x = A -> D = L )
  assume ovmpt2x.3: |- F = ( x e. C , y e. D |-> R )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint L x
  disjoint L y
  disjoint S x
  disjoint S y
  assert |- ( ( A e. C /\ B e. L /\ S e. H ) -> ( A F B ) = S )

  proof
    cS
    cH
    wcel
    cA
    cC
    wcel
    #
    cB
    cL
    wcel
    #
    cS
    cvv
    wcel
    #
    cA
    cB
    cF
    co
    cS
    wceq
    cS
    cH
    elex
    @0
    @1
    @2
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
    cvv
    cF
    vx
    vy
    cC
    cD
    cR
    cmpt2
    wceq
    @3
    ovmpt2x.3
    a1i
    vx
    cv
    cA
    wceq
    #
    vy
    cv
    cB
    wceq
    wa
    cR
    cS
    wceq
    @3
    ovmpt2x.1
    adantl
    @4
    cD
    cL
    wceq
    @3
    ovmpt2x.2
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
    ovmpt2dx
    syl3an3
end
