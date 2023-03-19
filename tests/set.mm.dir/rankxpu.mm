include "cxp.mm"
include "crnk.mm"
include "cfv.mm"
include "cun.mm"
include "cpw.mm"
include "csuc.mm"
include "wss.mm"
include "xpsspw.mm"
include "unex.mm"
include "pwex.mm"
include "rankss.mm"
include "ax-mp.mm"
include "rankpw.mm"
include "wceq.mm"
include "suceq.mm"
include "eqtri.mm"
include "sseqtri.mm"

theorem rankxpu
  let cA: class A
  let cB: class B
  assume rankxpl.1: |- A e. _V
  assume rankxpl.2: |- B e. _V


  assert |- ( rank ` ( A X. B ) ) C_ suc suc ( rank ` ( A u. B ) )

  proof
    cA
    cB
    cxp
    #
    crnk
    cfv
    #
    cA
    cB
    cun
    #
    cpw
    #
    cpw
    #
    crnk
    cfv
    #
    @2
    crnk
    cfv
    csuc
    #
    csuc
    #
    @0
    @4
    wss
    @1
    @5
    wss
    cA
    cB
    xpsspw
    @0
    @4
    @3
    @2
    cA
    cB
    rankxpl.1
    rankxpl.2
    unex
    #
    pwex
    #
    pwex
    rankss
    ax-mp
    @5
    @3
    crnk
    cfv
    #
    csuc
    #
    @7
    @3
    @9
    rankpw
    @10
    @6
    wceq
    @11
    @7
    wceq
    @2
    @8
    rankpw
    @10
    @6
    suceq
    ax-mp
    eqtri
    sseqtri
end
