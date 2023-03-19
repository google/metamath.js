include "ccoss.mm"
include "cid.mm"
include "wss.mm"
include "cv.mm"
include "wbr.mm"
include "wmo.mm"
include "wal.mm"
include "wceq.mm"
include "ccnv.mm"
include "cec.mm"
include "cin.mm"
include "c0.mm"
include "wo.mm"
include "crn.mm"
include "wral.mm"
include "cossssid4.mm"
include "ineccnvmo2.mm"
include "bitr4i.mm"

theorem cossssid5
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let vu: setvar u

  disjoint R x
  disjoint R y
  disjoint x y
  disjoint R u
  disjoint u x
  disjoint u y
  assert |- ( ,~ R C_ _I <-> A. x e. ran R A. y e. ran R ( x = y \/ ( [ x ] `' R i^i [ y ] `' R ) = (/) ) )

  proof
    cR
    ccoss
    cid
    wss
    vu
    cv
    vx
    cv
    #
    cR
    wbr
    vx
    wmo
    vu
    wal
    @0
    vy
    cv
    #
    wceq
    @0
    cR
    ccnv
    #
    cec
    @1
    @2
    cec
    cin
    c0
    wceq
    wo
    vy
    cR
    crn
    #
    wral
    vx
    @3
    wral
    vx
    vu
    cR
    cossssid4
    vx
    vy
    vu
    cR
    ineccnvmo2
    bitr4i
end
