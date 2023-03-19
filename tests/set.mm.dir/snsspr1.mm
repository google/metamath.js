include "csn.mm"
include "cun.mm"
include "cpr.mm"
include "ssun1.mm"
include "df-pr.mm"
include "sseqtr4i.mm"

theorem snsspr1
  let cA: class A
  let cB: class B


  assert |- { A } C_ { A , B }

  proof
    cA
    csn
    #
    @0
    cB
    csn
    #
    cun
    cA
    cB
    cpr
    @0
    @1
    ssun1
    cA
    cB
    df-pr
    sseqtr4i
end
