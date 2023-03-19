include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "copab.mm"
include "cmpt.mm"
include "wsb.mm"
include "nfv.mm"
include "nfs1v.mm"
include "nfan.mm"
include "weq.mm"
include "eleq1.mm"
include "sbequ12.mm"
include "anbi12d.mm"
include "cbvopab1.mm"
include "nfeq2.mm"
include "nfsb.mm"
include "sbequ.mm"
include "eqeq2d.mm"
include "sbie.mm"
include "syl6bb.mm"
include "eqtri.mm"
include "df-mpt.mm"
include "3eqtr4i.mm"

theorem cbvmpt
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vz: setvar z
  assume cbvmpt.1: |- F/_ y B
  assume cbvmpt.2: |- F/_ x C
  assume cbvmpt.3: |- ( x = y -> B = C )

  disjoint A x
  disjoint A y
  disjoint w z
  disjoint w x
  disjoint A w
  disjoint x z
  disjoint A z
  disjoint w y
  disjoint y z
  disjoint B w
  disjoint B z
  disjoint C w
  disjoint C z
  assert |- ( x e. A |-> B ) = ( y e. A |-> C )

  proof
    vx
    cv
    #
    cA
    wcel
    #
    vz
    cv
    #
    cB
    wceq
    #
    wa
    #
    vx
    vz
    copab
    #
    vy
    cv
    #
    cA
    wcel
    #
    @2
    cC
    wceq
    #
    wa
    #
    vy
    vz
    copab
    #
    vx
    cA
    cB
    cmpt
    vy
    cA
    cC
    cmpt
    @5
    vw
    cv
    #
    cA
    wcel
    #
    @3
    vx
    vw
    wsb
    #
    wa
    #
    vw
    vz
    copab
    @10
    @4
    @14
    vx
    vz
    vw
    @4
    vw
    nfv
    @12
    @13
    vx
    @12
    vx
    nfv
    @3
    vx
    vw
    nfs1v
    nfan
    vx
    vw
    weq
    @1
    @12
    @3
    @13
    @0
    @11
    cA
    eleq1
    @3
    vx
    vw
    sbequ12
    anbi12d
    cbvopab1
    @14
    @9
    vw
    vz
    vy
    @12
    @13
    vy
    @12
    vy
    nfv
    @3
    vx
    vw
    vy
    vy
    @2
    cB
    cbvmpt.1
    nfeq2
    nfsb
    nfan
    @9
    vw
    nfv
    vw
    vy
    weq
    #
    @12
    @7
    @13
    @8
    @11
    @6
    cA
    eleq1
    @15
    @13
    @3
    vx
    vy
    wsb
    @8
    @3
    vw
    vy
    vx
    sbequ
    @3
    @8
    vx
    vy
    vx
    @2
    cC
    cbvmpt.2
    nfeq2
    vx
    vy
    weq
    cB
    cC
    @2
    cbvmpt.3
    eqeq2d
    sbie
    syl6bb
    anbi12d
    cbvopab1
    eqtri
    vx
    vz
    cA
    cB
    df-mpt
    vy
    vz
    cA
    cC
    df-mpt
    3eqtr4i
end
