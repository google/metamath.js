include "ccoss.mm"
include "cid.mm"
include "wss.mm"
include "cv.mm"
include "wceq.mm"
include "copab.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "dfid3.mm"
include "sseq2i.mm"
include "df-coss.mm"
include "sseq1i.mm"
include "ssopab2b.mm"
include "3bitri.mm"

theorem cossssid2
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
  assert |- ( ,~ R C_ _I <-> A. x A. y ( E. u ( u R x /\ u R y ) -> x = y ) )

  proof
    cR
    ccoss
    #
    cid
    wss
    @0
    vx
    cv
    #
    vy
    cv
    #
    wceq
    #
    vx
    vy
    copab
    #
    wss
    vu
    cv
    #
    @1
    cR
    wbr
    @5
    @2
    cR
    wbr
    wa
    vu
    wex
    #
    vx
    vy
    copab
    #
    @4
    wss
    @6
    @3
    wi
    vy
    wal
    vx
    wal
    cid
    @4
    @0
    vx
    vy
    dfid3
    sseq2i
    @0
    @7
    @4
    vx
    vy
    vu
    cR
    df-coss
    sseq1i
    @6
    @3
    vx
    vy
    ssopab2b
    3bitri
end
