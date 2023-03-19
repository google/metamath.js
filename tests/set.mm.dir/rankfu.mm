include "wf.mm"
include "cxp.mm"
include "wss.mm"
include "crnk.mm"
include "cfv.mm"
include "cun.mm"
include "csuc.mm"
include "fssxp.mm"
include "xpex.mm"
include "rankss.mm"
include "rankxpu.mm"
include "syl6ss.mm"
include "syl.mm"

theorem rankfu
  let cA: class A
  let cB: class B
  let cF: class F
  assume rankxpl.1: |- A e. _V
  assume rankxpl.2: |- B e. _V


  assert |- ( F : A --> B -> ( rank ` F ) C_ suc suc ( rank ` ( A u. B ) ) )

  proof
    cA
    cB
    cF
    wf
    cF
    cA
    cB
    cxp
    #
    wss
    #
    cF
    crnk
    cfv
    #
    cA
    cB
    cun
    crnk
    cfv
    csuc
    csuc
    #
    wss
    cA
    cB
    cF
    fssxp
    @1
    @2
    @0
    crnk
    cfv
    @3
    cF
    @0
    cA
    cB
    rankxpl.1
    rankxpl.2
    xpex
    rankss
    cA
    cB
    rankxpl.1
    rankxpl.2
    rankxpu
    syl6ss
    syl
end
