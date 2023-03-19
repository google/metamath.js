include "csn.mm"
include "cpr.mm"
include "cun.mm"
include "ctp.mm"
include "ssun2.mm"
include "df-tp.mm"
include "sseqtr4i.mm"

theorem snsstp3
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- { C } C_ { A , B , C }

  proof
    cC
    csn
    #
    cA
    cB
    cpr
    #
    @0
    cun
    cA
    cB
    cC
    ctp
    @0
    @1
    ssun2
    cA
    cB
    cC
    df-tp
    sseqtr4i
end
