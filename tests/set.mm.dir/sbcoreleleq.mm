include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "w3o.mm"
include "wel.mm"
include "wsbc.mm"
include "weq.mm"
include "wb.mm"
include "sbcel2gv.mm"
include "sbcel1v.mm"
include "a1i.mm"
include "eqsbc3r.mm"
include "3orbi123.mm"
include "3impexpbicomi.mm"
include "syl3c.mm"
include "sbc3or.mm"
include "syl6rbbr.mm"

theorem sbcoreleleq
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cV: class V

  disjoint x y
  assert |- ( A e. V -> ( [. A / y ]. ( x e. y \/ y e. x \/ x = y ) <-> ( x e. A \/ A e. x \/ x = A ) ) )

  proof
    cA
    cV
    wcel
    #
    vx
    cv
    #
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
    vx
    vy
    wel
    #
    vy
    cA
    wsbc
    #
    vy
    vx
    wel
    #
    vy
    cA
    wsbc
    #
    vx
    vy
    weq
    #
    vy
    cA
    wsbc
    #
    w3o
    #
    @6
    @8
    @10
    w3o
    vy
    cA
    wsbc
    @0
    @7
    @2
    wb
    #
    @9
    @3
    wb
    #
    @11
    @4
    wb
    #
    @5
    @12
    wb
    vy
    @1
    cA
    cV
    sbcel2gv
    @14
    @0
    vy
    cA
    @1
    sbcel1v
    a1i
    vy
    cA
    @1
    cV
    eqsbc3r
    @13
    @14
    @15
    @12
    @5
    @7
    @2
    @9
    @3
    @11
    @4
    3orbi123
    3impexpbicomi
    syl3c
    @6
    @8
    @10
    vy
    cA
    sbc3or
    syl6rbbr
end
