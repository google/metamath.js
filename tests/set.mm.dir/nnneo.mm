include "com.mm"
include "wcel.mm"
include "c2o.mm"
include "comu.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "csuc.mm"
include "wa.mm"
include "wn.mm"
include "con0.mm"
include "nnon.mm"
include "onnbtwn.mm"
include "syl.mm"
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
include "2onn.mm"
include "nnmord.mm"
include "mp3an3.mm"
include "simpl.mm"
include "syl6bir.mm"
include "syl5.mm"
include "simpr.mm"
include "c1o.mm"
include "coa.mm"
include "nnmcl.mm"
include "mpan.mm"
include "oa1suc.mm"
include "3syl.mm"
include "1onn.mm"
include "elexi.mm"
include "df-2o.mm"
include "eleqtrri.mm"
include "nnaord.mm"
include "mp3an12.mm"
include "nnmsuc.mm"
include "eleqtrrd.mm"
include "eqeltrrd.mm"
include "ad2antrr.mm"
include "peano2.mm"
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

theorem nnneo
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. _om /\ B e. _om /\ C = ( 2o .o A ) ) -> -. suc C = ( 2o .o B ) )

  proof
    cA
    com
    wcel
    #
    cB
    com
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
    #
    @3
    @0
    cA
    con0
    wcel
    @12
    cA
    nnon
    cA
    cB
    onnbtwn
    syl
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
    @14
    wb
    @1
    @3
    @5
    @13
    @6
    cC
    @2
    suceq
    eqeq1d
    3ad2ant3
    @0
    @1
    @14
    @11
    wi
    @3
    @0
    @1
    wa
    #
    @14
    @8
    @10
    @14
    @2
    @6
    wcel
    #
    @15
    @8
    @14
    @2
    @13
    wcel
    @16
    @2
    c2o
    cA
    comu
    ovex
    sucid
    @13
    @6
    @2
    eleq2
    mpbii
    @15
    @16
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
    com
    wcel
    #
    @18
    @16
    wb
    2onn
    cA
    cB
    c2o
    nnmord
    mp3an3
    @8
    @17
    simpl
    syl6bir
    syl5
    @15
    @14
    @10
    @15
    @14
    wa
    #
    @10
    @17
    @20
    @10
    @17
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
    @20
    @13
    @6
    @22
    @15
    @14
    simpr
    @0
    @13
    @22
    wcel
    @1
    @14
    @0
    @2
    c1o
    coa
    co
    #
    @13
    @22
    @0
    @2
    com
    wcel
    #
    @2
    con0
    wcel
    @24
    @13
    wceq
    @19
    @0
    @25
    2onn
    c2o
    cA
    nnmcl
    mpan
    #
    @2
    nnon
    @2
    oa1suc
    3syl
    @0
    @24
    @2
    c2o
    coa
    co
    #
    @22
    @0
    c1o
    c2o
    wcel
    #
    @24
    @27
    wcel
    #
    c1o
    c1o
    csuc
    c2o
    c1o
    c1o
    com
    1onn
    elexi
    sucid
    df-2o
    eleqtrri
    @0
    @25
    @28
    @29
    wb
    #
    @26
    c1o
    com
    wcel
    @19
    @25
    @30
    1onn
    2onn
    c1o
    c2o
    @2
    nnaord
    mp3an12
    syl
    mpbii
    @19
    @0
    @22
    @27
    wceq
    2onn
    c2o
    cA
    nnmsuc
    mpan
    eleqtrrd
    eqeltrrd
    ad2antrr
    eqeltrrd
    @15
    @21
    @23
    wb
    #
    @14
    @1
    @0
    @31
    @0
    @1
    @9
    com
    wcel
    #
    @31
    cA
    peano2
    @1
    @32
    @19
    @31
    2onn
    cB
    @9
    c2o
    nnmord
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
