include "csn.mm"
include "cun.mm"
include "cpr.mm"
include "ssun2.mm"
include "df-pr.mm"
include "sseqtr4i.mm"

theorem snsspr2
  let cA: class A
  let cB: class B


  assert |- { B } C_ { A , B }

  proof
    cB
    csn
    #
    cA
    csn
    #
    @0
    cun
    cA
    cB
    cpr
    @0
    @1
    ssun2
    cA
    cB
    df-pr
    sseqtr4i
end
