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
include "elsng.mm"
include "orbi2d.mm"
include "syl5bb.mm"

theorem elsucg
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( A e. V -> ( A e. suc B <-> ( A e. B \/ A = B ) ) )

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
    cA
    cV
    wcel
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
    @8
    cA
    cB
    df-suc
    eleq2i
    cA
    cB
    @3
    elun
    bitri
    @6
    @4
    @7
    @2
    cA
    cB
    cV
    elsng
    orbi2d
    syl5bb
end
