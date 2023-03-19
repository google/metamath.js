include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "wf1.mm"
include "wex.mm"
include "cen.mm"
include "wss.mm"
include "wa.mm"
include "brdom.mm"
include "wf1o.mm"
include "vex.mm"
include "f11o.mm"
include "exbii.mm"
include "excom.mm"
include "bitri.mm"
include "bren.mm"
include "anbi1i.mm"
include "19.41v.mm"
include "bitr4i.mm"

theorem domen
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vf: setvar f
  assume bren.1: |- B e. _V

  disjoint A x
  disjoint B x
  disjoint f x
  disjoint A f
  disjoint B f
  assert |- ( A ~<_ B <-> E. x ( A ~~ x /\ x C_ B ) )

  proof
    cA
    cB
    cdom
    wbr
    cA
    cB
    vf
    cv
    #
    wf1
    #
    vf
    wex
    #
    cA
    vx
    cv
    #
    cen
    wbr
    #
    @3
    cB
    wss
    #
    wa
    #
    vx
    wex
    #
    cA
    cB
    vf
    bren.1
    brdom
    @2
    cA
    @3
    @0
    wf1o
    #
    @5
    wa
    #
    vf
    wex
    #
    vx
    wex
    #
    @7
    @2
    @9
    vx
    wex
    #
    vf
    wex
    @11
    @1
    @12
    vf
    vx
    cA
    cB
    @0
    vf
    vex
    f11o
    exbii
    @9
    vf
    vx
    excom
    bitri
    @6
    @10
    vx
    @6
    @8
    vf
    wex
    #
    @5
    wa
    @10
    @4
    @13
    @5
    cA
    @3
    vf
    bren
    anbi1i
    @8
    @5
    vf
    19.41v
    bitr4i
    exbii
    bitr4i
    bitri
end
