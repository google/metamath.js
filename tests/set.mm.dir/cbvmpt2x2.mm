include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "coprab.mm"
include "cmpt2.mm"
include "nfv.mm"
include "nfan.mm"
include "nfeq2.mm"
include "nfcri.mm"
include "weq.mm"
include "eleq1.mm"
include "eleq2d.mm"
include "sylan9bb.mm"
include "simpr.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "ancoms.mm"
include "eqeq2d.mm"
include "cbvoprab12.mm"
include "df-mpt2.mm"
include "3eqtr4i.mm"

theorem cbvmpt2x2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let vu: setvar u
  let vk: setvar k
  assume cbvmpt2x2.1: |- F/_ z A
  assume cbvmpt2x2.2: |- F/_ y D
  assume cbvmpt2x2.3: |- F/_ z C
  assume cbvmpt2x2.4: |- F/_ w C
  assume cbvmpt2x2.5: |- F/_ x E
  assume cbvmpt2x2.6: |- F/_ y E
  assume cbvmpt2x2.7: |- ( y = z -> A = D )
  assume cbvmpt2x2.8: |- ( ( y = z /\ x = w ) -> C = E )

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A w
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint D x
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint B u
  disjoint C u
  disjoint D u
  disjoint E u
  disjoint k x
  assert |- ( x e. A , y e. B |-> C ) = ( w e. D , z e. B |-> E )

  proof
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
    #
    vu
    cv
    #
    cC
    wceq
    #
    wa
    #
    vx
    vy
    vu
    coprab
    vw
    cv
    #
    cD
    wcel
    #
    vz
    cv
    #
    cB
    wcel
    #
    wa
    #
    @5
    cE
    wceq
    #
    wa
    #
    vw
    vz
    vu
    coprab
    vx
    vy
    cA
    cB
    cC
    cmpt2
    vw
    vz
    cD
    cB
    cE
    cmpt2
    @7
    @14
    vx
    vy
    vu
    vw
    vz
    @4
    @6
    vw
    @1
    @3
    vw
    @1
    vw
    nfv
    @3
    vw
    nfv
    nfan
    vw
    @5
    cC
    cbvmpt2x2.4
    nfeq2
    nfan
    @4
    @6
    vz
    @1
    @3
    vz
    vz
    vx
    cA
    cbvmpt2x2.1
    nfcri
    @3
    vz
    nfv
    nfan
    vz
    @5
    cC
    cbvmpt2x2.3
    nfeq2
    nfan
    @12
    @13
    vx
    @9
    @11
    vx
    @9
    vx
    nfv
    @11
    vx
    nfv
    nfan
    vx
    @5
    cE
    cbvmpt2x2.5
    nfeq2
    nfan
    @12
    @13
    vy
    @9
    @11
    vy
    vy
    vw
    cD
    cbvmpt2x2.2
    nfcri
    @11
    vy
    nfv
    nfan
    vy
    @5
    cE
    cbvmpt2x2.6
    nfeq2
    nfan
    vx
    vw
    weq
    #
    vy
    vz
    weq
    #
    wa
    #
    @4
    @12
    @6
    @13
    @17
    @1
    @9
    @3
    @11
    @15
    @1
    @8
    cA
    wcel
    @16
    @9
    @0
    @8
    cA
    eleq1
    @16
    cA
    cD
    @8
    cbvmpt2x2.7
    eleq2d
    sylan9bb
    @17
    @2
    @10
    cB
    @15
    @16
    simpr
    eleq1d
    anbi12d
    @17
    cC
    cE
    @5
    @16
    @15
    cC
    cE
    wceq
    cbvmpt2x2.8
    ancoms
    eqeq2d
    anbi12d
    cbvoprab12
    vx
    vy
    vu
    cA
    cB
    cC
    df-mpt2
    vw
    vz
    vu
    cD
    cB
    cE
    df-mpt2
    3eqtr4i
end
