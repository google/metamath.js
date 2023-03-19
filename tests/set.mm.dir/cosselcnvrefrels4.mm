include "ccoss.mm"
include "ccnvrefrels.mm"
include "wcel.mm"
include "cid.mm"
include "wss.mm"
include "crels.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wmo.mm"
include "wal.mm"
include "cosselcnvrefrels2.mm"
include "cossssid4.mm"
include "anbi1i.mm"
include "bitri.mm"

theorem cosselcnvrefrels4
  let vx: setvar x
  let vu: setvar u
  let cR: class R

  disjoint R u
  disjoint R x
  disjoint u x
  assert |- ( ,~ R e. CnvRefRels <-> ( A. u E* x u R x /\ ,~ R e. Rels ) )

  proof
    cR
    ccoss
    #
    ccnvrefrels
    wcel
    @0
    cid
    wss
    #
    @0
    crels
    wcel
    #
    wa
    vu
    cv
    vx
    cv
    cR
    wbr
    vx
    wmo
    vu
    wal
    #
    @2
    wa
    cR
    cosselcnvrefrels2
    @1
    @3
    @2
    vx
    vu
    cR
    cossssid4
    anbi1i
    bitri
end
