include "cen.mm"
include "wbr.mm"
include "wa.mm"
include "c0.mm"
include "csn.mm"
include "cxp.mm"
include "c1o.mm"
include "cun.mm"
include "ccda.mm"
include "co.mm"
include "cvv.mm"
include "wcel.mm"
include "relen.mm"
include "brrelexi.mm"
include "0ex.mm"
include "xpsneng.mm"
include "sylancl.mm"
include "brrelex2i.mm"
include "ensymd.mm"
include "entr.mm"
include "mpdan.mm"
include "syl2anc.mm"
include "con0.mm"
include "1on.mm"
include "cin.mm"
include "wceq.mm"
include "xp01disj.mm"
include "unen.mm"
include "mpanr12.mm"
include "syl2an.mm"
include "cdaval.mm"
include "3brtr4d.mm"

theorem cdaen
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A ~~ B /\ C ~~ D ) -> ( A +c C ) ~~ ( B +c D ) )

  proof
    cA
    cB
    cen
    wbr
    #
    cC
    cD
    cen
    wbr
    #
    wa
    cA
    c0
    csn
    #
    cxp
    #
    cC
    c1o
    csn
    #
    cxp
    #
    cun
    #
    cB
    @2
    cxp
    #
    cD
    @4
    cxp
    #
    cun
    #
    cA
    cC
    ccda
    co
    #
    cB
    cD
    ccda
    co
    #
    cen
    @0
    @3
    @7
    cen
    wbr
    #
    @5
    @8
    cen
    wbr
    #
    @6
    @9
    cen
    wbr
    #
    @1
    @0
    @3
    cA
    cen
    wbr
    #
    cA
    @7
    cen
    wbr
    #
    @12
    @0
    cA
    cvv
    wcel
    #
    c0
    cvv
    wcel
    #
    @15
    cA
    cB
    cen
    relen
    brrelexi
    #
    0ex
    cA
    c0
    cvv
    cvv
    xpsneng
    sylancl
    @0
    cB
    @7
    cen
    wbr
    @16
    @0
    @7
    cB
    @0
    cB
    cvv
    wcel
    #
    @18
    @7
    cB
    cen
    wbr
    cA
    cB
    cen
    relen
    brrelex2i
    #
    0ex
    cB
    c0
    cvv
    cvv
    xpsneng
    sylancl
    ensymd
    cA
    cB
    @7
    entr
    mpdan
    @3
    cA
    @7
    entr
    syl2anc
    @1
    @5
    cC
    cen
    wbr
    #
    cC
    @8
    cen
    wbr
    #
    @13
    @1
    cC
    cvv
    wcel
    #
    c1o
    con0
    wcel
    #
    @22
    cC
    cD
    cen
    relen
    brrelexi
    #
    1on
    cC
    c1o
    cvv
    con0
    xpsneng
    sylancl
    @1
    cD
    @8
    cen
    wbr
    @23
    @1
    @8
    cD
    @1
    cD
    cvv
    wcel
    #
    @25
    @8
    cD
    cen
    wbr
    cC
    cD
    cen
    relen
    brrelex2i
    #
    1on
    cD
    c1o
    cvv
    con0
    xpsneng
    sylancl
    ensymd
    cC
    cD
    @8
    entr
    mpdan
    @5
    cC
    @8
    entr
    syl2anc
    @12
    @13
    wa
    @3
    @5
    cin
    c0
    wceq
    @7
    @8
    cin
    c0
    wceq
    @14
    cA
    cC
    xp01disj
    cB
    cD
    xp01disj
    @3
    @7
    @5
    @8
    unen
    mpanr12
    syl2an
    @0
    @17
    @24
    @10
    @6
    wceq
    @1
    @19
    @26
    cA
    cC
    cvv
    cvv
    cdaval
    syl2an
    @0
    @20
    @27
    @11
    @9
    wceq
    @1
    @21
    @28
    cB
    cD
    cvv
    cvv
    cdaval
    syl2an
    3brtr4d
end
