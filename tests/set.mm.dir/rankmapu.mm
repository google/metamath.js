include "cmap.mm"
include "co.mm"
include "crnk.mm"
include "cfv.mm"
include "cxp.mm"
include "cpw.mm"
include "cun.mm"
include "csuc.mm"
include "wss.mm"
include "mapsspw.mm"
include "xpex.mm"
include "pwex.mm"
include "rankss.mm"
include "ax-mp.mm"
include "rankpw.mm"
include "rankxpu.mm"
include "wceq.mm"
include "uncom.mm"
include "fveq2i.mm"
include "suceq.mm"
include "sseqtri.mm"
include "word.mm"
include "wb.mm"
include "rankon.mm"
include "onordi.mm"
include "onsuci.mm"
include "ordsucsssuc.mm"
include "mp2an.mm"
include "mpbi.mm"
include "eqsstri.mm"
include "sstri.mm"

theorem rankmapu
  let cA: class A
  let cB: class B
  assume rankxpl.1: |- A e. _V
  assume rankxpl.2: |- B e. _V


  assert |- ( rank ` ( A ^m B ) ) C_ suc suc suc ( rank ` ( A u. B ) )

  proof
    cA
    cB
    cmap
    co
    #
    crnk
    cfv
    #
    cB
    cA
    cxp
    #
    cpw
    #
    crnk
    cfv
    #
    cA
    cB
    cun
    #
    crnk
    cfv
    #
    csuc
    #
    csuc
    #
    csuc
    #
    @0
    @3
    wss
    @1
    @4
    wss
    cA
    cB
    mapsspw
    @0
    @3
    @2
    cB
    cA
    rankxpl.2
    rankxpl.1
    xpex
    #
    pwex
    rankss
    ax-mp
    @4
    @2
    crnk
    cfv
    #
    csuc
    #
    @9
    @2
    @10
    rankpw
    @11
    @8
    wss
    #
    @12
    @9
    wss
    #
    @11
    cB
    cA
    cun
    #
    crnk
    cfv
    #
    csuc
    #
    csuc
    #
    @8
    cB
    cA
    rankxpl.2
    rankxpl.1
    rankxpu
    @17
    @7
    wceq
    #
    @18
    @8
    wceq
    @16
    @6
    wceq
    @19
    @15
    @5
    crnk
    cB
    cA
    uncom
    fveq2i
    @16
    @6
    suceq
    ax-mp
    @17
    @7
    suceq
    ax-mp
    sseqtri
    @11
    word
    @8
    word
    @13
    @14
    wb
    @11
    @2
    rankon
    onordi
    @8
    @7
    @6
    @5
    rankon
    onsuci
    onsuci
    onordi
    @11
    @8
    ordsucsssuc
    mp2an
    mpbi
    eqsstri
    sstri
end
