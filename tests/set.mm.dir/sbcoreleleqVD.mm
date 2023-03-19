include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "w3o.mm"
include "wsbc.mm"
include "wb.mm"
include "idn1.mm"
include "sbcel2gv.mm"
include "e1a.mm"
include "sbcel1gvOLD.mm"
include "eqsbc3r.mm"
include "3orbi123.mm"
include "3impexpbicomi.mm"
include "e111.mm"
include "sbc3orgOLD.mm"
include "biantr.mm"
include "expcom.mm"
include "e11.mm"
include "in1.mm"

theorem sbcoreleleqVD
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint x y
  assert |- ( A e. B -> ( [. A / y ]. ( x e. y \/ y e. x \/ x = y ) <-> ( x e. A \/ A e. x \/ x = A ) ) )

  proof
    cA
    cB
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    wcel
    #
    @2
    @1
    wcel
    #
    @1
    @2
    wceq
    #
    w3o
    vy
    cA
    wsbc
    #
    @1
    cA
    wcel
    #
    cA
    @1
    wcel
    #
    @1
    cA
    wceq
    #
    w3o
    #
    wb
    #
    @0
    @10
    @3
    vy
    cA
    wsbc
    #
    @4
    vy
    cA
    wsbc
    #
    @5
    vy
    cA
    wsbc
    #
    w3o
    #
    wb
    #
    @6
    @15
    wb
    #
    @11
    @0
    @12
    @7
    wb
    #
    @13
    @8
    wb
    #
    @14
    @9
    wb
    #
    @16
    @0
    @0
    @18
    @0
    idn1
    #
    vy
    @1
    cA
    cB
    sbcel2gv
    e1a
    @0
    @0
    @19
    @21
    vy
    cA
    @1
    cB
    sbcel1gvOLD
    e1a
    @0
    @0
    @20
    @21
    vy
    cA
    @1
    cB
    eqsbc3r
    e1a
    @18
    @19
    @20
    @15
    @10
    @12
    @7
    @13
    @8
    @14
    @9
    3orbi123
    3impexpbicomi
    e111
    @0
    @0
    @17
    @21
    @3
    @4
    @5
    vy
    cA
    cB
    sbc3orgOLD
    e1a
    @17
    @16
    @11
    @6
    @15
    @10
    biantr
    expcom
    e11
    in1
end
