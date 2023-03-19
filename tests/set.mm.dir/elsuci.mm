include "csuc.mm"
include "wcel.mm"
include "csn.mm"
include "wo.mm"
include "wceq.mm"
include "cun.mm"
include "df-suc.mm"
include "eleq2i.mm"
include "elun.mm"
include "bitri.mm"
include "elsni.mm"
include "orim2i.mm"
include "sylbi.mm"

theorem elsuci
  let cA: class A
  let cB: class B


  assert |- ( A e. suc B -> ( A e. B \/ A = B ) )

  proof
    cA
    cB
    csuc
    #
    wcel
    #
    cA
    cB
    wcel
    #
    cA
    cB
    csn
    #
    wcel
    #
    wo
    #
    @2
    cA
    cB
    wceq
    #
    wo
    @1
    cA
    cB
    @3
    cun
    #
    wcel
    @5
    @0
    @7
    cA
    cB
    df-suc
    eleq2i
    cA
    cB
    @3
    elun
    bitri
    @4
    @6
    @2
    cA
    cB
    elsni
    orim2i
    sylbi
end
