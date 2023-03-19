include "ccnv.mm"
include "ccoss.mm"
include "cid.mm"
include "wss.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "cossssid3.mm"
include "alrot3.mm"
include "wb.mm"
include "cvv.mm"
include "brcnvg.mm"
include "el2v.mm"
include "anbi12i.mm"
include "imbi1i.mm"
include "3albii.mm"
include "3bitri.mm"

theorem cosscnvssid3
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let cR: class R

  disjoint R u
  disjoint R v
  disjoint R x
  disjoint u v
  disjoint u x
  disjoint v x
  assert |- ( ,~ `' R C_ _I <-> A. u A. v A. x ( ( u R x /\ v R x ) -> u = v ) )

  proof
    cR
    ccnv
    #
    ccoss
    cid
    wss
    vx
    cv
    #
    vu
    cv
    #
    @0
    wbr
    #
    @1
    vv
    cv
    #
    @0
    wbr
    #
    wa
    #
    @2
    @4
    wceq
    #
    wi
    #
    vv
    wal
    vu
    wal
    vx
    wal
    @8
    vx
    wal
    vv
    wal
    vu
    wal
    @2
    @1
    cR
    wbr
    #
    @4
    @1
    cR
    wbr
    #
    wa
    #
    @7
    wi
    #
    vx
    wal
    vv
    wal
    vu
    wal
    vu
    vv
    vx
    @0
    cossssid3
    @8
    vx
    vu
    vv
    alrot3
    @8
    @12
    vu
    vv
    vx
    @6
    @11
    @7
    @3
    @9
    @5
    @10
    @3
    @9
    wb
    vx
    vu
    @1
    @2
    cvv
    cvv
    cR
    brcnvg
    el2v
    @5
    @10
    wb
    vx
    vv
    @1
    @4
    cvv
    cvv
    cR
    brcnvg
    el2v
    anbi12i
    imbi1i
    3albii
    3bitri
end
