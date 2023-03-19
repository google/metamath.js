include "ciun.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "cab.mm"
include "wa.mm"
include "wex.mm"
include "nfv.mm"
include "nf5i.mm"
include "nfan.mm"
include "weq.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "cbvex.mm"
include "df-rex.mm"
include "3bitr4i.mm"
include "abbii.mm"
include "df-iun.mm"
include "3eqtr4i.mm"
include "bnj1143.mm"
include "eqsstri.mm"

theorem bnj1146
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vw: setvar w
  assume bnj1146.1: |- ( y e. A -> A. x y e. A )

  disjoint A y
  disjoint B x
  disjoint B y
  disjoint x y
  disjoint A w
  disjoint w y
  disjoint B w
  disjoint w x
  assert |- U_ x e. A B C_ B

  proof
    vx
    cA
    cB
    ciun
    #
    vy
    cA
    cB
    ciun
    #
    cB
    vw
    cv
    cB
    wcel
    #
    vx
    cA
    wrex
    #
    vw
    cab
    @2
    vy
    cA
    wrex
    #
    vw
    cab
    @0
    @1
    @3
    @4
    vw
    vx
    cv
    #
    cA
    wcel
    #
    @2
    wa
    #
    vx
    wex
    vy
    cv
    #
    cA
    wcel
    #
    @2
    wa
    #
    vy
    wex
    @3
    @4
    @7
    @10
    vx
    vy
    @7
    vy
    nfv
    @9
    @2
    vx
    @9
    vx
    bnj1146.1
    nf5i
    @2
    vx
    nfv
    nfan
    vx
    vy
    weq
    @6
    @9
    @2
    @5
    @8
    cA
    eleq1
    anbi1d
    cbvex
    @2
    vx
    cA
    df-rex
    @2
    vy
    cA
    df-rex
    3bitr4i
    abbii
    vx
    vw
    cA
    cB
    df-iun
    vy
    vw
    cA
    cB
    df-iun
    3eqtr4i
    vy
    cA
    cB
    bnj1143
    eqsstri
end
