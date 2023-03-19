include "csn.mm"
include "cpr.mm"
include "cun.mm"
include "ctp.mm"
include "snsspr2.mm"
include "ssun1.mm"
include "sstri.mm"
include "df-tp.mm"
include "sseqtr4i.mm"

theorem snsstp2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- { B } C_ { A , B , C }

  proof
    cB
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
    snsspr2
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
