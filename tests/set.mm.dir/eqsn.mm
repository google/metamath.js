include "c0.mm"
include "wne.mm"
include "csn.mm"
include "wceq.mm"
include "wo.mm"
include "cv.mm"
include "wral.mm"
include "wn.mm"
include "wb.mm"
include "df-ne.mm"
include "biorf.mm"
include "sylbi.mm"
include "wss.mm"
include "wcel.mm"
include "dfss3.mm"
include "sssn.mm"
include "velsn.mm"
include "ralbii.mm"
include "3bitr3i.mm"
include "syl6bb.mm"

theorem eqsn
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
    c0
    wceq
    #
    @2
    wo
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
    @3
    wn
    @2
    @4
    wb
    cA
    c0
    df-ne
    @3
    @2
    biorf
    sylbi
    cA
    @1
    wss
    @5
    @1
    wcel
    #
    vx
    cA
    wral
    @4
    @7
    vx
    cA
    @1
    dfss3
    cA
    cB
    sssn
    @8
    @6
    vx
    cA
    vx
    cB
    velsn
    ralbii
    3bitr3i
    syl6bb
end
