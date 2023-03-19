include "ccnv.mm"
include "wss.mm"
include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "cres.mm"
include "wb.mm"
include "cv.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "wceq.mm"
include "wral.mm"
include "symrefref2.mm"
include "cnvsym.mm"
include "idinxpss.mm"
include "issref.mm"
include "bibi12i.mm"
include "3imtr3i.mm"

theorem symrefref3
  let vx: setvar x
  let vy: setvar y
  let cR: class R

  disjoint R x
  disjoint R y
  disjoint x y
  assert |- ( A. x A. y ( x R y -> y R x ) -> ( A. x e. dom R A. y e. ran R ( x = y -> x R y ) <-> A. x e. dom R x R x ) )

  proof
    cR
    ccnv
    cR
    wss
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
    cid
    @0
    cres
    cR
    wss
    #
    wb
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    @5
    @4
    cR
    wbr
    wi
    vy
    wal
    vx
    wal
    @4
    @5
    wceq
    @6
    wi
    vy
    @1
    wral
    vx
    @0
    wral
    #
    @4
    @4
    cR
    wbr
    vx
    @0
    wral
    #
    wb
    cR
    symrefref2
    vx
    vy
    cR
    cnvsym
    @2
    @7
    @3
    @8
    vx
    vy
    @0
    @1
    cR
    idinxpss
    vx
    @0
    cR
    issref
    bibi12i
    3imtr3i
end
