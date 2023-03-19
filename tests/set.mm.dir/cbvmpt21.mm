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
include "nfel.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "cbvoprab1.mm"
include "df-mpt2.mm"
include "3eqtr4i.mm"

theorem cbvmpt21
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cE: class E
  let vu: setvar u
  assume cbvmpt21.1: |- F/_ x B
  assume cbvmpt21.2: |- F/_ z B
  assume cbvmpt21.3: |- F/_ z C
  assume cbvmpt21.4: |- F/_ x E
  assume cbvmpt21.5: |- ( x = z -> C = E )

  disjoint A x
  disjoint A z
  disjoint x z
  disjoint x y
  disjoint y z
  disjoint A u
  disjoint u x
  disjoint u z
  disjoint B u
  disjoint C u
  disjoint E u
  disjoint u y
  assert |- ( x e. A , y e. B |-> C ) = ( z e. A , y e. B |-> E )

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
    @3
    wa
    #
    @5
    cE
    wceq
    #
    wa
    #
    vz
    vy
    vu
    coprab
    vx
    vy
    cA
    cB
    cC
    cmpt2
    vz
    vy
    cA
    cB
    cE
    cmpt2
    @7
    @12
    vx
    vy
    vu
    vz
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
    cbvmpt21.2
    nfcri
    nfan
    vz
    @5
    cC
    cbvmpt21.3
    nfeq2
    nfan
    @10
    @11
    vx
    @9
    @3
    vx
    @9
    vx
    nfv
    vx
    @2
    cB
    vx
    @2
    nfcv
    cbvmpt21.1
    nfel
    nfan
    vx
    @5
    cE
    cbvmpt21.4
    nfeq2
    nfan
    @0
    @8
    wceq
    #
    @4
    @10
    @6
    @11
    @13
    @1
    @9
    @3
    @0
    @8
    cA
    eleq1
    anbi1d
    @13
    cC
    cE
    @5
    cbvmpt21.5
    eqeq2d
    anbi12d
    cbvoprab1
    vx
    vy
    vu
    cA
    cB
    cC
    df-mpt2
    vz
    vy
    vu
    cA
    cB
    cE
    df-mpt2
    3eqtr4i
end
