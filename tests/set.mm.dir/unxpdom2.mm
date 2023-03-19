include "c1o.mm"
include "csdm.mm"
include "wbr.mm"
include "cdom.mm"
include "wa.mm"
include "cun.mm"
include "csn.mm"
include "cxp.mm"
include "c0.mm"
include "cin.mm"
include "wceq.mm"
include "cen.mm"
include "cvv.mm"
include "wcel.mm"
include "com.mm"
include "relsdom.mm"
include "brrelex2i.mm"
include "adantr.mm"
include "1onn.mm"
include "xpsneng.mm"
include "sylancl.mm"
include "ensymd.mm"
include "endom.mm"
include "syl.mm"
include "simpr.mm"
include "0ex.mm"
include "domentr.mm"
include "syl2anc.mm"
include "wne.mm"
include "1n0.mm"
include "xpsndisj.mm"
include "mp1i.mm"
include "undom.mm"
include "syl21anc.mm"
include "sdomentr.mm"
include "syldan.mm"
include "unxpdom.mm"
include "xpen.mm"
include "domtr.mm"

theorem unxpdom2
  let cA: class A
  let cB: class B


  assert |- ( ( 1o ~< A /\ B ~<_ A ) -> ( A u. B ) ~<_ ( A X. A ) )

  proof
    c1o
    cA
    csdm
    wbr
    #
    cB
    cA
    cdom
    wbr
    #
    wa
    #
    cA
    cB
    cun
    #
    cA
    c1o
    csn
    cxp
    #
    cA
    c0
    csn
    cxp
    #
    cun
    #
    cdom
    wbr
    #
    @6
    cA
    cA
    cxp
    #
    cdom
    wbr
    #
    @3
    @8
    cdom
    wbr
    @2
    cA
    @4
    cdom
    wbr
    #
    cB
    @5
    cdom
    wbr
    #
    @4
    @5
    cin
    c0
    wceq
    #
    @7
    @2
    cA
    @4
    cen
    wbr
    #
    @10
    @2
    @4
    cA
    @2
    cA
    cvv
    wcel
    #
    c1o
    com
    wcel
    @4
    cA
    cen
    wbr
    #
    @0
    @14
    @1
    c1o
    cA
    csdm
    relsdom
    brrelex2i
    adantr
    #
    1onn
    cA
    c1o
    cvv
    com
    xpsneng
    sylancl
    #
    ensymd
    #
    cA
    @4
    endom
    syl
    @2
    @1
    cA
    @5
    cen
    wbr
    #
    @11
    @0
    @1
    simpr
    @2
    @5
    cA
    @2
    @14
    c0
    cvv
    wcel
    @5
    cA
    cen
    wbr
    #
    @16
    0ex
    cA
    c0
    cvv
    cvv
    xpsneng
    sylancl
    #
    ensymd
    #
    cB
    cA
    @5
    domentr
    syl2anc
    c1o
    c0
    wne
    @12
    @2
    1n0
    cA
    c1o
    cA
    c0
    xpsndisj
    mp1i
    cA
    @4
    cB
    @5
    undom
    syl21anc
    @2
    @6
    @4
    @5
    cxp
    #
    cdom
    wbr
    #
    @23
    @8
    cen
    wbr
    #
    @9
    @2
    c1o
    @4
    csdm
    wbr
    #
    c1o
    @5
    csdm
    wbr
    #
    @24
    @0
    @1
    @13
    @26
    @18
    c1o
    cA
    @4
    sdomentr
    syldan
    @0
    @1
    @19
    @27
    @22
    c1o
    cA
    @5
    sdomentr
    syldan
    @4
    @5
    unxpdom
    syl2anc
    @2
    @15
    @20
    @25
    @17
    @21
    @4
    cA
    @5
    cA
    xpen
    syl2anc
    @6
    @23
    @8
    domentr
    syl2anc
    @3
    @6
    @8
    domtr
    syl2anc
end
