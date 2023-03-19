include "cid.mm"
include "cv.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "wss.mm"
include "wceq.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "crels.mm"
include "crefrels.mm"
include "dfrefrels2.mm"
include "idinxpss.mm"
include "rabbieq.mm"

theorem dfrefrels3
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r

  disjoint r x
  disjoint r y
  disjoint x y
  assert |- RefRels = { r e. Rels | A. x e. dom r A. y e. ran r ( x = y -> x r y ) }

  proof
    cid
    vr
    cv
    #
    cdm
    #
    @0
    crn
    #
    cxp
    cin
    @0
    wss
    vx
    cv
    #
    vy
    cv
    #
    wceq
    @3
    @4
    @0
    wbr
    wi
    vy
    @2
    wral
    vx
    @1
    wral
    vr
    crels
    crefrels
    vr
    dfrefrels2
    vx
    vy
    @1
    @2
    @0
    idinxpss
    rabbieq
end
