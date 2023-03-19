include "cv.mm"
include "cdom.mm"
include "wbr.mm"
include "cen.mm"
include "wss.mm"
include "wa.mm"
include "wex.mm"
include "breq2.mm"
include "wceq.mm"
include "sseq2.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "vex.mm"
include "domen.mm"
include "vtoclbg.mm"

theorem domeng
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( B e. C -> ( A ~<_ B <-> E. x ( A ~~ x /\ x C_ B ) ) )

  proof
    cA
    vy
    cv
    #
    cdom
    wbr
    cA
    vx
    cv
    #
    cen
    wbr
    #
    @1
    @0
    wss
    #
    wa
    #
    vx
    wex
    cA
    cB
    cdom
    wbr
    @2
    @1
    cB
    wss
    #
    wa
    #
    vx
    wex
    vy
    cB
    cC
    @0
    cB
    cA
    cdom
    breq2
    @0
    cB
    wceq
    #
    @4
    @6
    vx
    @7
    @3
    @5
    @2
    @0
    cB
    @1
    sseq2
    anbi2d
    exbidv
    vx
    cA
    @0
    vy
    vex
    domen
    vtoclbg
end
