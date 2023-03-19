include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "copab.mm"
include "ccnv.mm"
include "cxp.mm"
include "cnvopab.mm"
include "ancom.mm"
include "opabbii.mm"
include "eqtri.mm"
include "df-xp.mm"
include "cnveqi.mm"
include "3eqtr4i.mm"

theorem cnvxp
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- `' ( A X. B ) = ( B X. A )

  proof
    vy
    cv
    cA
    wcel
    #
    vx
    cv
    cB
    wcel
    #
    wa
    #
    vy
    vx
    copab
    #
    ccnv
    #
    @1
    @0
    wa
    #
    vx
    vy
    copab
    #
    cA
    cB
    cxp
    #
    ccnv
    cB
    cA
    cxp
    @4
    @2
    vx
    vy
    copab
    @6
    @2
    vy
    vx
    cnvopab
    @2
    @5
    vx
    vy
    @0
    @1
    ancom
    opabbii
    eqtri
    @7
    @3
    vy
    vx
    cA
    cB
    df-xp
    cnveqi
    vx
    vy
    cB
    cA
    df-xp
    3eqtr4i
end
