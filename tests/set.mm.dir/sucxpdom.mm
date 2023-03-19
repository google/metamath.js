include "c1o.mm"
include "csdm.mm"
include "wbr.mm"
include "csuc.mm"
include "csn.mm"
include "cun.mm"
include "cxp.mm"
include "cdom.mm"
include "df-suc.mm"
include "c0.mm"
include "cen.mm"
include "cin.mm"
include "wceq.mm"
include "cvv.mm"
include "wcel.mm"
include "con0.mm"
include "relsdom.mm"
include "brrelex2i.mm"
include "1on.mm"
include "xpsneng.mm"
include "sylancl.mm"
include "ensymd.mm"
include "endom.mm"
include "syl.mm"
include "ensn1g.mm"
include "ensdomtr.mm"
include "mpancom.mm"
include "0ex.mm"
include "sdomentr.mm"
include "syl2anc.mm"
include "sdomdom.mm"
include "wne.mm"
include "1n0.mm"
include "xpsndisj.mm"
include "mp1i.mm"
include "undom.mm"
include "syl21anc.mm"
include "mpdan.mm"
include "unxpdom.mm"
include "domtr.mm"
include "xpen.mm"
include "domentr.mm"
include "syl5eqbr.mm"

theorem sucxpdom
  let cA: class A


  assert |- ( 1o ~< A -> suc A ~<_ ( A X. A ) )

  proof
    c1o
    cA
    csdm
    wbr
    #
    cA
    csuc
    cA
    cA
    csn
    #
    cun
    #
    cA
    cA
    cxp
    #
    cdom
    cA
    df-suc
    @0
    @2
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
    cxp
    #
    cdom
    wbr
    #
    @6
    @3
    cen
    wbr
    #
    @2
    @3
    cdom
    wbr
    @0
    @2
    @4
    @5
    cun
    #
    cdom
    wbr
    #
    @9
    @6
    cdom
    wbr
    #
    @7
    @0
    cA
    @4
    cdom
    wbr
    #
    @1
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
    @10
    @0
    cA
    @4
    cen
    wbr
    #
    @12
    @0
    @4
    cA
    @0
    cA
    cvv
    wcel
    #
    c1o
    con0
    wcel
    @4
    cA
    cen
    wbr
    #
    c1o
    cA
    csdm
    relsdom
    brrelex2i
    #
    1on
    cA
    c1o
    cvv
    con0
    xpsneng
    sylancl
    #
    ensymd
    #
    cA
    @4
    endom
    syl
    @0
    @1
    @5
    csdm
    wbr
    #
    @13
    @0
    @1
    cA
    csdm
    wbr
    #
    cA
    @5
    cen
    wbr
    #
    @21
    @1
    c1o
    cen
    wbr
    #
    @0
    @22
    @0
    @16
    @24
    @18
    cA
    cvv
    ensn1g
    syl
    @1
    c1o
    cA
    ensdomtr
    mpancom
    @0
    @5
    cA
    @0
    @16
    c0
    cvv
    wcel
    @5
    cA
    cen
    wbr
    #
    @18
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
    @1
    cA
    @5
    sdomentr
    syl2anc
    @1
    @5
    sdomdom
    syl
    c1o
    c0
    wne
    @14
    @0
    1n0
    cA
    c1o
    cA
    c0
    xpsndisj
    mp1i
    cA
    @4
    @1
    @5
    undom
    syl21anc
    @0
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
    @11
    @0
    @15
    @28
    @20
    c1o
    cA
    @4
    sdomentr
    mpdan
    @0
    @23
    @29
    @27
    c1o
    cA
    @5
    sdomentr
    mpdan
    @4
    @5
    unxpdom
    syl2anc
    @2
    @9
    @6
    domtr
    syl2anc
    @0
    @17
    @25
    @8
    @19
    @26
    @4
    cA
    @5
    cA
    xpen
    syl2anc
    @2
    @6
    @3
    domentr
    syl2anc
    syl5eqbr
end
