include "wcnvrefrel.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "cid.mm"
include "wss.mm"
include "wrel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "df-cnvrefrel.mm"
include "inxpssidinxp.mm"
include "anbi1i.mm"
include "bitri.mm"

theorem dfcnvrefrel3
  let vx: setvar x
  let vy: setvar y
  let cR: class R

  disjoint R x
  disjoint R y
  disjoint x y
  assert |- ( CnvRefRel R <-> ( A. x e. dom R A. y e. ran R ( x R y -> x = y ) /\ Rel R ) )

  proof
    cR
    wcnvrefrel
    cR
    cR
    cdm
    #
    cR
    crn
    #
    cxp
    #
    cin
    cid
    @2
    cin
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
    cR
    wbr
    @5
    @6
    wceq
    wi
    vy
    @1
    wral
    vx
    @0
    wral
    #
    @4
    wa
    cR
    df-cnvrefrel
    @3
    @7
    @4
    vx
    vy
    @0
    @1
    cR
    inxpssidinxp
    anbi1i
    bitri
end
