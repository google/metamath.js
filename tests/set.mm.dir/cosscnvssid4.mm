include "ccnv.mm"
include "ccoss.mm"
include "cid.mm"
include "wss.mm"
include "cv.mm"
include "wbr.mm"
include "wmo.mm"
include "wal.mm"
include "cossssid4.mm"
include "wb.mm"
include "cvv.mm"
include "brcnvg.mm"
include "el2v.mm"
include "mobii.mm"
include "albii.mm"
include "bitri.mm"

theorem cosscnvssid4
  let vx: setvar x
  let vu: setvar u
  let cR: class R

  disjoint R u
  disjoint R x
  disjoint u x
  assert |- ( ,~ `' R C_ _I <-> A. x E* u u R x )

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
    vu
    wmo
    #
    vx
    wal
    @2
    @1
    cR
    wbr
    #
    vu
    wmo
    #
    vx
    wal
    vu
    vx
    @0
    cossssid4
    @4
    @6
    vx
    @3
    @5
    vu
    @3
    @5
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
    mobii
    albii
    bitri
end
