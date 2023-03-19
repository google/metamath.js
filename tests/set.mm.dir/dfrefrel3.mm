include "wrefrel.mm"
include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "wss.mm"
include "wrel.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "dfrefrel2.mm"
include "idinxpss.mm"
include "anbi1i.mm"
include "bitri.mm"

theorem dfrefrel3
  let vx: setvar x
  let vy: setvar y
  let cR: class R

  disjoint R x
  disjoint R y
  disjoint x y
  assert |- ( RefRel R <-> ( A. x e. dom R A. y e. ran R ( x = y -> x R y ) /\ Rel R ) )

  proof
    cR
    wrefrel
    cid
    cR
    cdm
    #
    cR
    crn
    #
    cxp
    cin
    cR
    wss
    #
    cR
    wrel
    #
    wa
    vx
    cv
    #
    vy
    cv
    #
    wceq
    @4
    @5
    cR
    wbr
    wi
    vy
    @1
    wral
    vx
    @0
    wral
    #
    @3
    wa
    cR
    dfrefrel2
    @2
    @6
    @3
    vx
    vy
    @0
    @1
    cR
    idinxpss
    anbi1i
    bitri
end
