include "cop.mm"
include "wne.mm"
include "wceq.mm"
include "wn.mm"
include "wcel.mm"
include "wa.mm"
include "wo.mm"
include "df-ne.mm"
include "opthg.mm"
include "notbid.mm"
include "ianor.mm"
include "orbi12i.mm"
include "bitr4i.mm"
include "syl6bb.mm"
include "syl5bb.mm"

theorem opthneg
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( <. A , B >. =/= <. C , D >. <-> ( A =/= C \/ B =/= D ) ) )

  proof
    cA
    cB
    cop
    #
    cC
    cD
    cop
    #
    wne
    @0
    @1
    wceq
    #
    wn
    #
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    #
    cA
    cC
    wne
    #
    cB
    cD
    wne
    #
    wo
    #
    @0
    @1
    df-ne
    @4
    @3
    cA
    cC
    wceq
    #
    cB
    cD
    wceq
    #
    wa
    #
    wn
    #
    @7
    @4
    @2
    @10
    cA
    cB
    cC
    cD
    cV
    cW
    opthg
    notbid
    @11
    @8
    wn
    #
    @9
    wn
    #
    wo
    @7
    @8
    @9
    ianor
    @5
    @12
    @6
    @13
    cA
    cC
    df-ne
    cB
    cD
    df-ne
    orbi12i
    bitr4i
    syl6bb
    syl5bb
end
