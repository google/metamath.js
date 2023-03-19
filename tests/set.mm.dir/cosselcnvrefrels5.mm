include "ccoss.mm"
include "ccnvrefrels.mm"
include "wcel.mm"
include "cid.mm"
include "wss.mm"
include "crels.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "ccnv.mm"
include "cec.mm"
include "cin.mm"
include "c0.mm"
include "wo.mm"
include "crn.mm"
include "wral.mm"
include "cosselcnvrefrels2.mm"
include "cossssid5.mm"
include "anbi1i.mm"
include "bitri.mm"

theorem cosselcnvrefrels5
  let vx: setvar x
  let vy: setvar y
  let cR: class R

  disjoint R x
  disjoint R y
  disjoint x y
  assert |- ( ,~ R e. CnvRefRels <-> ( A. x e. ran R A. y e. ran R ( x = y \/ ( [ x ] `' R i^i [ y ] `' R ) = (/) ) /\ ,~ R e. Rels ) )

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
    vx
    cv
    #
    vy
    cv
    #
    wceq
    @3
    cR
    ccnv
    #
    cec
    @4
    @5
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
    @6
    wral
    #
    @2
    wa
    cR
    cosselcnvrefrels2
    @1
    @7
    @2
    vx
    vy
    cR
    cossssid5
    anbi1i
    bitri
end
