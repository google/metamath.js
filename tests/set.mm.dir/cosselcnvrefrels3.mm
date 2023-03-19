include "ccoss.mm"
include "ccnvrefrels.mm"
include "wcel.mm"
include "cid.mm"
include "wss.mm"
include "crels.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "cosselcnvrefrels2.mm"
include "cossssid3.mm"
include "anbi1i.mm"
include "bitri.mm"

theorem cosselcnvrefrels3
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
  assert |- ( ,~ R e. CnvRefRels <-> ( A. u A. x A. y ( ( u R x /\ u R y ) -> x = y ) /\ ,~ R e. Rels ) )

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
    #
    vx
    cv
    #
    cR
    wbr
    @3
    vy
    cv
    #
    cR
    wbr
    wa
    @4
    @5
    wceq
    wi
    vy
    wal
    vx
    wal
    vu
    wal
    #
    @2
    wa
    cR
    cosselcnvrefrels2
    @1
    @6
    @2
    vx
    vy
    vu
    cR
    cossssid3
    anbi1i
    bitri
end
