include "wcel.mm"
include "w3a.mm"
include "c2.mm"
include "cwwlksnon.mm"
include "co.mm"
include "cv.mm"
include "cs3.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "c1.mm"
include "cfv.mm"
include "simpr.mm"
include "cwwlksn.mm"
include "cc0.mm"
include "wb.mm"
include "wwlknonOLD.mm"
include "3adant1.mm"
include "wi.mm"
include "cvtx.mm"
include "cword.mm"
include "chash.mm"
include "caddc.mm"
include "wwlknbp2OLD.mm"
include "c3.mm"
include "2p1e3.mm"
include "eqeq2i.mm"
include "cfzo.mm"
include "ctp.mm"
include "1ex.mm"
include "tpid2.mm"
include "oveq2.mm"
include "fzo0to3tp.mm"
include "syl6eq.mm"
include "syl5eleqr.mm"
include "wrdsymbcl.mm"
include "sylan2.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "simpl.mm"
include "eqidd.mm"
include "3jca.mm"
include "3ad2ant2.mm"
include "eqcomi.mm"
include "wrdeqi.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "simpl32.mm"
include "adantl.mm"
include "simpl33.mm"
include "eqwrds3.mm"
include "syl13anc.mm"
include "mpbir2and.mm"
include "jca.mm"
include "mpdan.mm"
include "3exp.mm"
include "sylan2b.mm"
include "syl.mm"
include "3impib.mm"
include "com12.mm"
include "sylbid.mm"
include "imp.mm"
include "anass.mm"
include "sylanbrc.mm"
include "id.mm"
include "s3eqd.mm"
include "eqeq2.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "biimpac.mm"
include "rspcedvd.mm"
include "ex.mm"
include "eqcoms.mm"
include "biimpa.mm"
include "a1i.mm"
include "rexlimdvw.mm"
include "impbid.mm"

theorem elwwlks2ons3OLD
  let cA: class A
  let cC: class C
  let cU: class U
  let cG: class G
  let cV: class V
  let cW: class W
  let vb: setvar b
  assume wwlks2onv.v: |- V = ( Vtx ` G )

  disjoint A b
  disjoint C b
  disjoint G b
  disjoint V b
  disjoint W b
  disjoint U b
  assert |- ( ( G e. U /\ A e. V /\ C e. V ) -> ( W e. ( A ( 2 WWalksNOn G ) C ) <-> E. b e. V ( W = <" A b C "> /\ <" A b C "> e. ( A ( 2 WWalksNOn G ) C ) ) ) )

  proof
    cG
    cU
    wcel
    #
    cA
    cV
    wcel
    #
    cC
    cV
    wcel
    #
    w3a
    #
    cW
    cA
    cC
    c2
    cG
    cwwlksnon
    co
    co
    #
    wcel
    #
    cW
    cA
    vb
    cv
    #
    cC
    cs3
    #
    wceq
    #
    @7
    @4
    wcel
    #
    wa
    #
    vb
    cV
    wrex
    #
    @3
    @5
    @11
    @3
    @5
    wa
    #
    @5
    cW
    cA
    c1
    cW
    cfv
    #
    cC
    cs3
    #
    wceq
    #
    wa
    #
    @13
    cV
    wcel
    #
    wa
    #
    @11
    @12
    @5
    @15
    @17
    wa
    #
    @18
    @3
    @5
    simpr
    @3
    @5
    @19
    @3
    @5
    cW
    c2
    cG
    cwwlksn
    co
    wcel
    #
    cc0
    cW
    cfv
    cA
    wceq
    #
    c2
    cW
    cfv
    cC
    wceq
    #
    w3a
    #
    @19
    @1
    @2
    @5
    @23
    wb
    @0
    cA
    cC
    cG
    c2
    cV
    cW
    wwlks2onv.v
    wwlknonOLD
    3adant1
    @23
    @3
    @19
    @20
    @21
    @22
    @3
    @19
    wi
    #
    @20
    cW
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    #
    cW
    chash
    cfv
    #
    c2
    c1
    caddc
    co
    #
    wceq
    #
    wa
    @21
    @22
    wa
    #
    @24
    wi
    #
    cG
    c2
    cW
    wwlknbp2OLD
    @30
    @27
    @28
    c3
    wceq
    #
    @32
    @29
    c3
    @28
    2p1e3
    eqeq2i
    @27
    @33
    wa
    #
    @31
    @3
    @19
    @34
    @31
    @3
    w3a
    #
    @13
    @25
    wcel
    #
    @19
    @34
    @31
    @36
    @3
    @33
    @27
    c1
    cc0
    @28
    cfzo
    co
    #
    wcel
    @36
    @33
    c1
    cc0
    c1
    c2
    ctp
    #
    @37
    cc0
    c1
    c2
    1ex
    tpid2
    @33
    @37
    cc0
    c3
    cfzo
    co
    @38
    @28
    c3
    cc0
    cfzo
    oveq2
    fzo0to3tp
    syl6eq
    syl5eleqr
    c1
    @25
    cW
    wrdsymbcl
    sylan2
    3ad2ant1
    @35
    @36
    wa
    #
    @15
    @17
    @39
    @15
    @33
    @21
    @13
    @13
    wceq
    #
    @22
    w3a
    #
    @35
    @33
    @36
    @34
    @31
    @33
    @3
    @27
    @33
    simpr
    3ad2ant1
    adantr
    @35
    @41
    @36
    @31
    @34
    @41
    @3
    @31
    @21
    @40
    @22
    @21
    @22
    simpl
    @31
    @13
    eqidd
    @21
    @22
    simpr
    3jca
    3ad2ant2
    adantr
    @39
    cW
    cV
    cword
    #
    wcel
    #
    @1
    @17
    @2
    @15
    @33
    @41
    wa
    wb
    @35
    @43
    @36
    @34
    @31
    @43
    @3
    @27
    @43
    @33
    @27
    @43
    @26
    @42
    cW
    @25
    cV
    cV
    @25
    wwlks2onv.v
    eqcomi
    #
    wrdeqi
    eleq2i
    biimpi
    adantr
    3ad2ant1
    adantr
    @0
    @1
    @2
    @34
    @31
    @36
    simpl32
    @36
    @17
    @35
    @36
    @17
    @25
    cV
    @13
    @44
    eleq2i
    biimpi
    adantl
    #
    @0
    @1
    @2
    @34
    @31
    @36
    simpl33
    cA
    @13
    cC
    cV
    cW
    eqwrds3
    syl13anc
    mpbir2and
    @45
    jca
    mpdan
    3exp
    sylan2b
    syl
    3impib
    com12
    sylbid
    imp
    @5
    @15
    @17
    anass
    sylanbrc
    @18
    @10
    @15
    @14
    @4
    wcel
    #
    wa
    #
    vb
    @13
    cV
    @16
    @17
    simpr
    @6
    @13
    wceq
    #
    @10
    @47
    wb
    #
    @18
    @48
    @7
    @14
    wceq
    #
    @49
    @48
    cA
    @6
    cC
    cC
    cA
    @13
    @48
    cA
    eqidd
    @48
    id
    @48
    cC
    eqidd
    s3eqd
    @50
    @8
    @15
    @9
    @46
    @7
    @14
    cW
    eqeq2
    @7
    @14
    @4
    eleq1
    anbi12d
    syl
    adantl
    @16
    @47
    @17
    @16
    @15
    @46
    @5
    @15
    simpr
    @15
    @5
    @46
    cW
    @14
    @4
    eleq1
    biimpac
    jca
    adantr
    rspcedvd
    syl
    ex
    @3
    @10
    @5
    vb
    cV
    @10
    @5
    wi
    @3
    @8
    @9
    @5
    @9
    @5
    wb
    @7
    cW
    @7
    cW
    @4
    eleq1
    eqcoms
    biimpa
    a1i
    rexlimdvw
    impbid
end
