include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "coprab.mm"
include "cmpt2.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "nfcv.mm"
include "nfral.mm"
include "wb.mm"
include "rsp.mm"
include "eqeq2.mm"
include "syl6.mm"
include "pm5.32d.mm"
include "eleq2.mm"
include "anbi1d.mm"
include "sylan9bbr.mm"
include "anass.mm"
include "3bitr4g.mm"
include "oprabbid.mm"
include "df-mpt2.mm"
include "3eqtr4g.mm"

theorem mpt2eq123
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint D x
  disjoint D y
  disjoint E y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint D z
  disjoint E z
  disjoint C z
  disjoint F z
  assert |- ( ( A = D /\ A. x e. A ( B = E /\ A. y e. B C = F ) ) -> ( x e. A , y e. B |-> C ) = ( x e. D , y e. E |-> F ) )

  proof
    cA
    cD
    wceq
    #
    cB
    cE
    wceq
    #
    cC
    cF
    wceq
    #
    vy
    cB
    wral
    #
    wa
    #
    vx
    cA
    wral
    #
    wa
    #
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    vz
    cv
    #
    cC
    wceq
    #
    wa
    #
    vx
    vy
    vz
    coprab
    @7
    cD
    wcel
    #
    @9
    cE
    wcel
    #
    wa
    @11
    cF
    wceq
    #
    wa
    #
    vx
    vy
    vz
    coprab
    vx
    vy
    cA
    cB
    cC
    cmpt2
    vx
    vy
    cD
    cE
    cF
    cmpt2
    @6
    @13
    @17
    vx
    vy
    vz
    @0
    @5
    vx
    @0
    vx
    nfv
    @4
    vx
    cA
    nfra1
    nfan
    @0
    @5
    vy
    @0
    vy
    nfv
    @4
    vy
    vx
    cA
    vy
    cA
    nfcv
    @1
    @3
    vy
    @1
    vy
    nfv
    @2
    vy
    cB
    nfra1
    nfan
    nfral
    nfan
    @6
    vz
    nfv
    @6
    @8
    @10
    @12
    wa
    #
    wa
    #
    @14
    @15
    @16
    wa
    #
    wa
    #
    @13
    @17
    @5
    @19
    @8
    @20
    wa
    @0
    @21
    @5
    @8
    @18
    @20
    @5
    @8
    @4
    @18
    @20
    wb
    @4
    vx
    cA
    rsp
    @3
    @18
    @10
    @16
    wa
    @1
    @20
    @3
    @10
    @12
    @16
    @3
    @10
    @2
    @12
    @16
    wb
    @2
    vy
    cB
    rsp
    cC
    cF
    @11
    eqeq2
    syl6
    pm5.32d
    @1
    @10
    @15
    @16
    cB
    cE
    @9
    eleq2
    anbi1d
    sylan9bbr
    syl6
    pm5.32d
    @0
    @8
    @14
    @20
    cA
    cD
    @7
    eleq2
    anbi1d
    sylan9bbr
    @8
    @10
    @12
    anass
    @14
    @15
    @16
    anass
    3bitr4g
    oprabbid
    vx
    vy
    vz
    cA
    cB
    cC
    df-mpt2
    vx
    vy
    vz
    cD
    cE
    cF
    df-mpt2
    3eqtr4g
end
