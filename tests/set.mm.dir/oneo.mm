include "con0.mm"
include "wcel.mm"
include "c2o.mm"
include "comu.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "csuc.mm"
include "wa.mm"
include "wn.mm"
include "onnbtwn.mm"
include "3ad2ant1.mm"
include "wb.mm"
include "suceq.mm"
include "eqeq1d.mm"
include "3ad2ant3.mm"
include "wi.mm"
include "ovex.mm"
include "sucid.mm"
include "eleq2.mm"
include "mpbii.mm"
include "c0.mm"
include "2on.mm"
include "omord.mm"
include "mp3an3.mm"
include "simpl.mm"
include "syl6bir.mm"
include "syl5.mm"
include "simpr.mm"
include "c1o.mm"
include "coa.mm"
include "omcl.mm"
include "mpan.mm"
include "oa1suc.mm"
include "syl.mm"
include "1on.mm"
include "elexi.mm"
include "df-2o.mm"
include "eleqtrri.mm"
include "oaord.mm"
include "mp3an12.mm"
include "omsuc.mm"
include "eleqtrrd.mm"
include "eqeltrrd.mm"
include "ad2antrr.mm"
include "suceloni.mm"
include "sylan2.mm"
include "ancoms.mm"
include "adantr.mm"
include "mpbird.mm"
include "simpld.mm"
include "ex.mm"
include "jcad.mm"
include "3adant3.mm"
include "sylbid.mm"
include "mtod.mm"

theorem oneo
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. On /\ B e. On /\ C = ( 2o .o A ) ) -> -. suc C = ( 2o .o B ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    cC
    c2o
    cA
    comu
    co
    #
    wceq
    #
    w3a
    #
    cC
    csuc
    #
    c2o
    cB
    comu
    co
    #
    wceq
    #
    cA
    cB
    wcel
    #
    cB
    cA
    csuc
    #
    wcel
    #
    wa
    #
    @0
    @1
    @11
    wn
    @3
    cA
    cB
    onnbtwn
    3ad2ant1
    @4
    @7
    @2
    csuc
    #
    @6
    wceq
    #
    @11
    @3
    @0
    @7
    @13
    wb
    @1
    @3
    @5
    @12
    @6
    cC
    @2
    suceq
    eqeq1d
    3ad2ant3
    @0
    @1
    @13
    @11
    wi
    @3
    @0
    @1
    wa
    #
    @13
    @8
    @10
    @13
    @2
    @6
    wcel
    #
    @14
    @8
    @13
    @2
    @12
    wcel
    @15
    @2
    c2o
    cA
    comu
    ovex
    sucid
    @12
    @6
    @2
    eleq2
    mpbii
    @14
    @15
    @8
    c0
    c2o
    wcel
    #
    wa
    #
    @8
    @0
    @1
    c2o
    con0
    wcel
    #
    @17
    @15
    wb
    2on
    cA
    cB
    c2o
    omord
    mp3an3
    @8
    @16
    simpl
    syl6bir
    syl5
    @14
    @13
    @10
    @14
    @13
    wa
    #
    @10
    @16
    @19
    @10
    @16
    wa
    #
    @6
    c2o
    @9
    comu
    co
    #
    wcel
    #
    @19
    @12
    @6
    @21
    @14
    @13
    simpr
    @0
    @12
    @21
    wcel
    @1
    @13
    @0
    @2
    c1o
    coa
    co
    #
    @12
    @21
    @0
    @2
    con0
    wcel
    #
    @23
    @12
    wceq
    @18
    @0
    @24
    2on
    c2o
    cA
    omcl
    mpan
    #
    @2
    oa1suc
    syl
    @0
    @23
    @2
    c2o
    coa
    co
    #
    @21
    @0
    c1o
    c2o
    wcel
    #
    @23
    @26
    wcel
    #
    c1o
    c1o
    csuc
    c2o
    c1o
    c1o
    con0
    1on
    elexi
    sucid
    df-2o
    eleqtrri
    @0
    @24
    @27
    @28
    wb
    #
    @25
    c1o
    con0
    wcel
    @18
    @24
    @29
    1on
    2on
    c1o
    c2o
    @2
    oaord
    mp3an12
    syl
    mpbii
    @18
    @0
    @21
    @26
    wceq
    2on
    c2o
    cA
    omsuc
    mpan
    eleqtrrd
    eqeltrrd
    ad2antrr
    eqeltrrd
    @14
    @20
    @22
    wb
    #
    @13
    @1
    @0
    @30
    @0
    @1
    @9
    con0
    wcel
    #
    @30
    cA
    suceloni
    @1
    @31
    @18
    @30
    2on
    cB
    @9
    c2o
    omord
    mp3an3
    sylan2
    ancoms
    adantr
    mpbird
    simpld
    ex
    jcad
    3adant3
    sylbid
    mtod
end
