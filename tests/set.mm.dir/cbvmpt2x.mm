include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "coprab.mm"
include "cmpt2.mm"
include "nfv.mm"
include "nfcri.mm"
include "nfan.mm"
include "nfeq2.mm"
include "nfcv.mm"
include "weq.mm"
include "wb.mm"
include "eleq1.mm"
include "adantr.mm"
include "eleq2d.mm"
include "sylan9bb.mm"
include "anbi12d.mm"
include "eqeq2d.mm"
include "cbvoprab12.mm"
include "df-mpt2.mm"
include "3eqtr4i.mm"

theorem cbvmpt2x
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
  assume cbvmpt2x.1: |- F/_ z B
  assume cbvmpt2x.2: |- F/_ x D
  assume cbvmpt2x.3: |- F/_ z C
  assume cbvmpt2x.4: |- F/_ w C
  assume cbvmpt2x.5: |- F/_ x E
  assume cbvmpt2x.6: |- F/_ y E
  assume cbvmpt2x.7: |- ( x = z -> B = D )
  assume cbvmpt2x.8: |- ( ( x = z /\ y = w ) -> C = E )

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint D y
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint B u
  disjoint C u
  disjoint D u
  disjoint E u
  assert |- ( x e. A , y e. B |-> C ) = ( z e. A , w e. D |-> E )

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
    vz
    cv
    #
    cA
    wcel
    #
    vw
    cv
    #
    cD
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
    vz
    vw
    vu
    coprab
    vx
    vy
    cA
    cB
    cC
    cmpt2
    vz
    vw
    cA
    cD
    cE
    cmpt2
    @7
    @14
    vx
    vy
    vu
    vz
    vw
    @4
    @6
    vz
    @1
    @3
    vz
    @1
    vz
    nfv
    vz
    vy
    cB
    cbvmpt2x.1
    nfcri
    nfan
    vz
    @5
    cC
    cbvmpt2x.3
    nfeq2
    nfan
    @4
    @6
    vw
    @1
    @3
    vw
    @1
    vw
    nfv
    vw
    vy
    cB
    vw
    cB
    nfcv
    nfcri
    nfan
    vw
    @5
    cC
    cbvmpt2x.4
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
    vx
    vw
    cD
    cbvmpt2x.2
    nfcri
    nfan
    vx
    @5
    cE
    cbvmpt2x.5
    nfeq2
    nfan
    @12
    @13
    vy
    @12
    vy
    nfv
    vy
    @5
    cE
    cbvmpt2x.6
    nfeq2
    nfan
    vx
    vz
    weq
    #
    vy
    vw
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
    @9
    wb
    @16
    @0
    @8
    cA
    eleq1
    adantr
    @15
    @3
    @2
    cD
    wcel
    @16
    @11
    @15
    cB
    cD
    @2
    cbvmpt2x.7
    eleq2d
    @2
    @10
    cD
    eleq1
    sylan9bb
    anbi12d
    @17
    cC
    cE
    @5
    cbvmpt2x.8
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
    vz
    vw
    vu
    cA
    cD
    cE
    df-mpt2
    3eqtr4i
end
