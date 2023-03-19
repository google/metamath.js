include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "coprab.mm"
include "cmpt2.mm"
include "nfcri.mm"
include "nfcv.mm"
include "nfan.mm"
include "nfeq2.mm"
include "nfv.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "cbvoprab2.mm"
include "df-mpt2.mm"
include "3eqtr4i.mm"

theorem cbvmpt22
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cE: class E
  let vu: setvar u
  assume cbvmpt22.1: |- F/_ y A
  assume cbvmpt22.2: |- F/_ w A
  assume cbvmpt22.3: |- F/_ w C
  assume cbvmpt22.4: |- F/_ y E
  assume cbvmpt22.5: |- ( y = w -> C = E )

  disjoint B w
  disjoint B y
  disjoint w y
  disjoint w x
  disjoint x y
  disjoint A u
  disjoint B u
  disjoint u w
  disjoint u y
  disjoint C u
  disjoint E u
  disjoint u x
  assert |- ( x e. A , y e. B |-> C ) = ( x e. A , w e. B |-> E )

  proof
    vx
    cv
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
    @0
    vw
    cv
    #
    cB
    wcel
    #
    wa
    #
    @4
    cE
    wceq
    #
    wa
    #
    vx
    vw
    vu
    coprab
    vx
    vy
    cA
    cB
    cC
    cmpt2
    vx
    vw
    cA
    cB
    cE
    cmpt2
    @6
    @11
    vx
    vy
    vu
    vw
    @3
    @5
    vw
    @0
    @2
    vw
    vw
    vx
    cA
    cbvmpt22.2
    nfcri
    vw
    vy
    cB
    vw
    cB
    nfcv
    nfcri
    nfan
    vw
    @4
    cC
    cbvmpt22.3
    nfeq2
    nfan
    @9
    @10
    vy
    @0
    @8
    vy
    vy
    vx
    cA
    cbvmpt22.1
    nfcri
    @8
    vy
    nfv
    nfan
    vy
    @4
    cE
    cbvmpt22.4
    nfeq2
    nfan
    @1
    @7
    wceq
    #
    @3
    @9
    @5
    @10
    @12
    @2
    @8
    @0
    @1
    @7
    cB
    eleq1
    anbi2d
    @12
    cC
    cE
    @4
    cbvmpt22.5
    eqeq2d
    anbi12d
    cbvoprab2
    vx
    vy
    vu
    cA
    cB
    cC
    df-mpt2
    vx
    vw
    vu
    cA
    cB
    cE
    df-mpt2
    3eqtr4i
end
