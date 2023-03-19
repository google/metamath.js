include "csn.mm"
include "cun.mm"
include "csuc.mm"
include "ssun1.mm"
include "df-suc.mm"
include "sseqtr4i.mm"

theorem sssucid
  let cA: class A


  assert |- A C_ suc A

  proof
    cA
    cA
    cA
    csn
    #
    cun
    cA
    csuc
    cA
    @0
    ssun1
    cA
    df-suc
    sseqtr4i
end
