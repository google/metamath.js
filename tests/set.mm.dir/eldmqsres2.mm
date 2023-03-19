include "wcel.mm"
include "cres.mm"
include "cdm.mm"
include "cqs.mm"
include "cv.mm"
include "cec.mm"
include "wex.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "eldmqsres.mm"
include "df-rex.mm"
include "19.41v.mm"
include "bitri.mm"
include "rexbii.mm"
include "syl6bbr.mm"

theorem eldmqsres2
  let vx: setvar x
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V

  disjoint A u
  disjoint A x
  disjoint u x
  disjoint B u
  disjoint B x
  disjoint R u
  disjoint R x
  assert |- ( B e. V -> ( B e. ( dom ( R |` A ) /. ( R |` A ) ) <-> E. u e. A E. x e. [ u ] R B = [ u ] R ) )

  proof
    cB
    cV
    wcel
    cB
    cR
    cA
    cres
    #
    cdm
    @0
    cqs
    wcel
    vx
    cv
    vu
    cv
    cR
    cec
    #
    wcel
    #
    vx
    wex
    cB
    @1
    wceq
    #
    wa
    #
    vu
    cA
    wrex
    @3
    vx
    @1
    wrex
    #
    vu
    cA
    wrex
    vx
    vu
    cA
    cB
    cR
    cV
    eldmqsres
    @5
    @4
    vu
    cA
    @5
    @2
    @3
    wa
    vx
    wex
    @4
    @3
    vx
    @1
    df-rex
    @2
    @3
    vx
    19.41v
    bitri
    rexbii
    syl6bbr
end
