include "cpr.mm"
include "csn.mm"
include "cun.mm"
include "cv.mm"
include "wceq.mm"
include "wo.mm"
include "cab.mm"
include "df-pr.mm"
include "wcel.mm"
include "elun.mm"
include "velsn.mm"
include "orbi12i.mm"
include "bitri.mm"
include "abbi2i.mm"
include "eqtri.mm"

theorem dfpr2
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- { A , B } = { x | ( x = A \/ x = B ) }

  proof
    cA
    cB
    cpr
    cA
    csn
    #
    cB
    csn
    #
    cun
    #
    vx
    cv
    #
    cA
    wceq
    #
    @3
    cB
    wceq
    #
    wo
    #
    vx
    cab
    cA
    cB
    df-pr
    @6
    vx
    @2
    @3
    @2
    wcel
    @3
    @0
    wcel
    #
    @3
    @1
    wcel
    #
    wo
    @6
    @3
    @0
    @1
    elun
    @7
    @4
    @8
    @5
    vx
    cA
    velsn
    vx
    cB
    velsn
    orbi12i
    bitri
    abbi2i
    eqtri
end
