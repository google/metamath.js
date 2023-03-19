include "csn.mm"
include "cpr.mm"
include "cun.mm"
include "ctp.mm"
include "snsspr1.mm"
include "ssun1.mm"
include "sstri.mm"
include "df-tp.mm"
include "sseqtr4i.mm"

theorem snsstp1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- { A } C_ { A , B , C }

  proof
    cA
    csn
    #
    cA
    cB
    cpr
    #
    cC
    csn
    #
    cun
    #
    cA
    cB
    cC
    ctp
    @0
    @1
    @3
    cA
    cB
    snsspr1
    @1
    @2
    ssun1
    sstri
    cA
    cB
    cC
    df-tp
    sseqtr4i
end
