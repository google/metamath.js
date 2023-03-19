include "wcel.mm"
include "cpr.mm"
include "csn.mm"
include "wo.mm"
include "wceq.mm"
include "ctp.mm"
include "w3o.mm"
include "elprg.mm"
include "elsng.mm"
include "orbi12d.mm"
include "cun.mm"
include "df-tp.mm"
include "eleq2i.mm"
include "elun.mm"
include "bitri.mm"
include "df-3or.mm"
include "3bitr4g.mm"

theorem eltpg
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V


  assert |- ( A e. V -> ( A e. { B , C , D } <-> ( A = B \/ A = C \/ A = D ) ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cB
    cC
    cpr
    #
    wcel
    #
    cA
    cD
    csn
    #
    wcel
    #
    wo
    #
    cA
    cB
    wceq
    #
    cA
    cC
    wceq
    #
    wo
    #
    cA
    cD
    wceq
    #
    wo
    cA
    cB
    cC
    cD
    ctp
    #
    wcel
    #
    @6
    @7
    @9
    w3o
    @0
    @2
    @8
    @4
    @9
    cA
    cB
    cC
    cV
    elprg
    cA
    cD
    cV
    elsng
    orbi12d
    @11
    cA
    @1
    @3
    cun
    #
    wcel
    @5
    @10
    @12
    cA
    cB
    cC
    cD
    df-tp
    eleq2i
    cA
    @1
    @3
    elun
    bitri
    @6
    @7
    @9
    df-3or
    3bitr4g
end
