include "ccoss.mm"
include "cid.mm"
include "wss.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "cossssid2.mm"
include "19.23v.mm"
include "albii.mm"
include "alcom.mm"
include "bitr3i.mm"
include "3bitri.mm"

theorem cossssid3
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cR: class R

  disjoint R u
  disjoint R x
  disjoint R y
  disjoint u x
  disjoint u y
  disjoint x y
  assert |- ( ,~ R C_ _I <-> A. u A. x A. y ( ( u R x /\ u R y ) -> x = y ) )

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
    @0
    vy
    cv
    #
    cR
    wbr
    wa
    #
    vu
    wex
    @1
    @2
    wceq
    #
    wi
    #
    vy
    wal
    #
    vx
    wal
    @3
    @4
    wi
    #
    vy
    wal
    #
    vu
    wal
    #
    vx
    wal
    @8
    vx
    wal
    vu
    wal
    vx
    vy
    vu
    cR
    cossssid2
    @6
    @9
    vx
    @6
    @7
    vu
    wal
    #
    vy
    wal
    @9
    @10
    @5
    vy
    @3
    @4
    vu
    19.23v
    albii
    @7
    vy
    vu
    alcom
    bitr3i
    albii
    @8
    vx
    vu
    alcom
    3bitri
end
