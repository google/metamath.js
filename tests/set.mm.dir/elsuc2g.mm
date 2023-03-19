include "csuc.mm"
include "wcel.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "wo.mm"
include "df-suc.mm"
include "eleq2i.mm"
include "elun.mm"
include "elsn2g.mm"
include "orbi2d.mm"
include "syl5bb.mm"

theorem elsuc2g
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( B e. V -> ( A e. suc B <-> ( A e. B \/ A = B ) ) )

  proof
    cA
    cB
    csuc
    #
    wcel
    cA
    cB
    cB
    csn
    #
    cun
    #
    wcel
    #
    cB
    cV
    wcel
    #
    cA
    cB
    wcel
    #
    cA
    cB
    wceq
    #
    wo
    #
    @0
    @2
    cA
    cB
    df-suc
    eleq2i
    @3
    @5
    cA
    @1
    wcel
    #
    wo
    @4
    @7
    cA
    cB
    @1
    elun
    @4
    @8
    @6
    @5
    cA
    cB
    cV
    elsn2g
    orbi2d
    syl5bb
    syl5bb
end
