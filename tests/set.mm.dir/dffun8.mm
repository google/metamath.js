include "wfun.mm"
include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "wmo.mm"
include "cdm.mm"
include "wral.mm"
include "wa.mm"
include "weu.mm"
include "dffun7.mm"
include "wex.mm"
include "wi.mm"
include "wcel.mm"
include "df-mo.mm"
include "wb.mm"
include "vex.mm"
include "eldm.mm"
include "pm5.5.mm"
include "sylbi.mm"
include "syl5bb.mm"
include "ralbiia.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem dffun8
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( Fun A <-> ( Rel A /\ A. x e. dom A E! y x A y ) )

  proof
    cA
    wfun
    cA
    wrel
    #
    vx
    cv
    #
    vy
    cv
    cA
    wbr
    #
    vy
    wmo
    #
    vx
    cA
    cdm
    #
    wral
    #
    wa
    @0
    @2
    vy
    weu
    #
    vx
    @4
    wral
    #
    wa
    vx
    vy
    cA
    dffun7
    @5
    @7
    @0
    @3
    @6
    vx
    @4
    @3
    @2
    vy
    wex
    #
    @6
    wi
    #
    @1
    @4
    wcel
    #
    @6
    @2
    vy
    df-mo
    @10
    @8
    @9
    @6
    wb
    vy
    @1
    cA
    vx
    vex
    eldm
    @8
    @6
    pm5.5
    sylbi
    syl5bb
    ralbiia
    anbi2i
    bitri
end
