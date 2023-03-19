include "ccoss.mm"
include "cid.mm"
include "wss.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wmo.mm"
include "cossssid3.mm"
include "breq2.mm"
include "mo4.mm"
include "albii.mm"
include "bitr4i.mm"

theorem cossssid4
  let vx: setvar x
  let vu: setvar u
  let cR: class R
  let vy: setvar y

  disjoint R u
  disjoint R x
  disjoint u x
  disjoint R y
  disjoint u y
  disjoint x y
  assert |- ( ,~ R C_ _I <-> A. u E* x u R x )

  proof
    cR
    ccoss
    cid
    wss
    vu
    cv
    #
    vx
    cv
    #
    cR
    wbr
    #
    @0
    vy
    cv
    #
    cR
    wbr
    #
    wa
    @1
    @3
    wceq
    wi
    vy
    wal
    vx
    wal
    #
    vu
    wal
    @2
    vx
    wmo
    #
    vu
    wal
    vx
    vy
    vu
    cR
    cossssid3
    @6
    @5
    vu
    @2
    @4
    vx
    vy
    @1
    @3
    @0
    cR
    breq2
    mo4
    albii
    bitr4i
end
