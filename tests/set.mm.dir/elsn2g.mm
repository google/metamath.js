include "wcel.mm"
include "csn.mm"
include "wceq.mm"
include "elsni.mm"
include "snidg.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "impbid2.mm"

theorem elsn2g
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( B e. V -> ( A e. { B } <-> A = B ) )

  proof
    cB
    cV
    wcel
    #
    cA
    cB
    csn
    #
    wcel
    #
    cA
    cB
    wceq
    #
    cA
    cB
    elsni
    @0
    @2
    @3
    cB
    @1
    wcel
    cB
    cV
    snidg
    cA
    cB
    @1
    eleq1
    syl5ibrcom
    impbid2
end
