include "c0.mm"
include "wne.mm"
include "csn.mm"
include "wceq.mm"
include "wss.mm"
include "cv.mm"
include "wral.mm"
include "eqimss.mm"
include "wn.mm"
include "df-ne.mm"
include "wo.mm"
include "sssn.mm"
include "biimpi.mm"
include "ord.mm"
include "syl5bi.mm"
include "com12.mm"
include "impbid2.mm"
include "wcel.mm"
include "dfss3.mm"
include "velsn.mm"
include "ralbii.mm"
include "bitri.mm"
include "syl6bb.mm"

theorem eqsnOLD
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A =/= (/) -> ( A = { B } <-> A. x e. A x = B ) )

  proof
    cA
    c0
    wne
    #
    cA
    cB
    csn
    #
    wceq
    #
    cA
    @1
    wss
    #
    vx
    cv
    #
    cB
    wceq
    #
    vx
    cA
    wral
    #
    @0
    @2
    @3
    cA
    @1
    eqimss
    @3
    @0
    @2
    @0
    cA
    c0
    wceq
    #
    wn
    @3
    @2
    cA
    c0
    df-ne
    @3
    @7
    @2
    @3
    @7
    @2
    wo
    cA
    cB
    sssn
    biimpi
    ord
    syl5bi
    com12
    impbid2
    @3
    @4
    @1
    wcel
    #
    vx
    cA
    wral
    @6
    vx
    cA
    @1
    dfss3
    @8
    @5
    vx
    cA
    vx
    cB
    velsn
    ralbii
    bitri
    syl6bb
end
