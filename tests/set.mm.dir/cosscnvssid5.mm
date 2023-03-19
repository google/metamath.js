include "ccnv.mm"
include "ccoss.mm"
include "cid.mm"
include "wss.mm"
include "wrel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wmo.mm"
include "wal.mm"
include "wceq.mm"
include "cec.mm"
include "cin.mm"
include "c0.mm"
include "wo.mm"
include "cdm.mm"
include "wral.mm"
include "cosscnvssid4.mm"
include "anbi1i.mm"
include "inecmo3.mm"
include "bitr4i.mm"

theorem cosscnvssid5
  let vv: setvar v
  let vu: setvar u
  let cR: class R
  let vx: setvar x

  disjoint R u
  disjoint R v
  disjoint u v
  disjoint R x
  disjoint u x
  disjoint v x
  assert |- ( ( ,~ `' R C_ _I /\ Rel R ) <-> ( A. u e. dom R A. v e. dom R ( u = v \/ ( [ u ] R i^i [ v ] R ) = (/) ) /\ Rel R ) )

  proof
    cR
    ccnv
    ccoss
    cid
    wss
    #
    cR
    wrel
    #
    wa
    vu
    cv
    #
    vx
    cv
    cR
    wbr
    vu
    wmo
    vx
    wal
    #
    @1
    wa
    @2
    vv
    cv
    #
    wceq
    @2
    cR
    cec
    @4
    cR
    cec
    cin
    c0
    wceq
    wo
    vv
    cR
    cdm
    #
    wral
    vu
    @5
    wral
    @1
    wa
    @0
    @3
    @1
    vx
    vu
    cR
    cosscnvssid4
    anbi1i
    vx
    vv
    vu
    cR
    inecmo3
    bitr4i
end
