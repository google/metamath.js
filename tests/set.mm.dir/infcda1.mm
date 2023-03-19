include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "c1o.mm"
include "ccda.mm"
include "co.mm"
include "c0.mm"
include "csn.mm"
include "cxp.mm"
include "cen.mm"
include "cop.mm"
include "cdif.mm"
include "cun.mm"
include "cvv.mm"
include "wcel.mm"
include "con0.mm"
include "wceq.mm"
include "reldom.mm"
include "brrelex2i.mm"
include "1on.mm"
include "cdaval.mm"
include "sylancl.mm"
include "df1o2.mm"
include "xpeq1i.mm"
include "0ex.mm"
include "elexi.mm"
include "xpsn.mm"
include "eqtr2i.mm"
include "a1i.mm"
include "difeq12d.mm"
include "difun2.mm"
include "cin.mm"
include "xp01disj.mm"
include "disj3.mm"
include "mpbi.mm"
include "eqtr4i.mm"
include "syl6eq.mm"
include "cdadom3.mm"
include "domtr.mm"
include "mpdan.mm"
include "infdifsn.mm"
include "syl.mm"
include "eqbrtrrd.mm"
include "ensymd.mm"
include "xpsneng.mm"
include "entr.mm"
include "syl2anc.mm"

theorem infcda1
  let cA: class A


  assert |- ( _om ~<_ A -> ( A +c 1o ) ~~ A )

  proof
    com
    cA
    cdom
    wbr
    #
    cA
    c1o
    ccda
    co
    #
    cA
    c0
    csn
    #
    cxp
    #
    cen
    wbr
    @3
    cA
    cen
    wbr
    #
    @1
    cA
    cen
    wbr
    @0
    @3
    @1
    @0
    @1
    c0
    c1o
    cop
    #
    csn
    #
    cdif
    #
    @3
    @1
    cen
    @0
    @7
    @3
    c1o
    c1o
    csn
    #
    cxp
    #
    cun
    #
    @9
    cdif
    #
    @3
    @0
    @1
    @10
    @6
    @9
    @0
    cA
    cvv
    wcel
    #
    c1o
    con0
    wcel
    #
    @1
    @10
    wceq
    com
    cA
    cdom
    reldom
    brrelex2i
    #
    1on
    cA
    c1o
    cvv
    con0
    cdaval
    sylancl
    @6
    @9
    wceq
    @0
    @9
    @2
    @8
    cxp
    @6
    c1o
    @2
    @8
    df1o2
    xpeq1i
    c0
    c1o
    0ex
    c1o
    con0
    1on
    elexi
    xpsn
    eqtr2i
    a1i
    difeq12d
    @11
    @3
    @9
    cdif
    #
    @3
    @3
    @9
    difun2
    @3
    @9
    cin
    c0
    wceq
    @3
    @15
    wceq
    cA
    c1o
    xp01disj
    @3
    @9
    disj3
    mpbi
    eqtr4i
    syl6eq
    @0
    com
    @1
    cdom
    wbr
    #
    @7
    @1
    cen
    wbr
    @0
    cA
    @1
    cdom
    wbr
    #
    @16
    @0
    @12
    @13
    @17
    @14
    1on
    cA
    c1o
    cvv
    con0
    cdadom3
    sylancl
    com
    cA
    @1
    domtr
    mpdan
    @1
    @5
    infdifsn
    syl
    eqbrtrrd
    ensymd
    @0
    @12
    c0
    cvv
    wcel
    @4
    @14
    0ex
    cA
    c0
    cvv
    cvv
    xpsneng
    sylancl
    @1
    @3
    cA
    entr
    syl2anc
end
