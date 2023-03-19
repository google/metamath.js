include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cxad.mm"
include "co.mm"
include "w3a.mm"
include "cr.mm"
include "cpnf.mm"
include "wceq.mm"
include "cmnf.mm"
include "xaddcl.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "simp1l.mm"
include "simp2r.mm"
include "syl2anc.mm"
include "3ad2ant2.mm"
include "simp3r.mm"
include "wb.mm"
include "simp1r.mm"
include "simprl.mm"
include "xltadd2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "simp3l.mm"
include "simp2l.mm"
include "simprr.mm"
include "xltadd1.mm"
include "xrlttrd.mm"
include "anassrs.mm"
include "wne.mm"
include "pnfxr.mm"
include "a1i.mm"
include "cle.mm"
include "pnfge.mm"
include "syl.mm"
include "xrltletrd.mm"
include "nltpnft.mm"
include "necon2abid.mm"
include "xaddnepnf.mm"
include "syl22anc.mm"
include "mpbird.mm"
include "oveq2.mm"
include "mnfxr.mm"
include "mnfle.mm"
include "xrlelttrd.mm"
include "ngtmnft.mm"
include "xaddpnf1.mm"
include "sylan9eqr.mm"
include "breqtrrd.mm"
include "adantlr.mm"
include "wn.mm"
include "a1d.mm"
include "necon4bd.mm"
include "imp.mm"
include "w3o.mm"
include "elxr.mm"
include "sylib.mm"
include "mpjao3dan.mm"
include "oveq1.mm"
include "xaddmnf2.mm"
include "xaddnemnf.mm"
include "eqbrtrd.mm"
include "3expia.mm"

theorem xlt2add
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. RR* /\ B e. RR* ) /\ ( C e. RR* /\ D e. RR* ) ) -> ( ( A < C /\ B < D ) -> ( A +e B ) < ( C +e D ) ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    wa
    #
    cC
    cxr
    wcel
    #
    cD
    cxr
    wcel
    #
    wa
    #
    cA
    cC
    clt
    wbr
    #
    cB
    cD
    clt
    wbr
    #
    wa
    #
    cA
    cB
    cxad
    co
    #
    cC
    cD
    cxad
    co
    #
    clt
    wbr
    #
    @2
    @5
    @8
    w3a
    #
    cA
    cr
    wcel
    #
    @11
    cA
    cpnf
    wceq
    #
    cA
    cmnf
    wceq
    #
    @12
    @13
    wa
    cD
    cr
    wcel
    #
    @11
    cD
    cpnf
    wceq
    #
    cD
    cmnf
    wceq
    #
    @12
    @13
    @16
    @11
    @12
    @13
    @16
    wa
    #
    wa
    #
    @9
    cA
    cD
    cxad
    co
    #
    @10
    @12
    @9
    cxr
    wcel
    #
    @19
    @2
    @5
    @22
    @8
    cA
    cB
    xaddcl
    3ad2ant1
    #
    adantr
    @12
    @21
    cxr
    wcel
    #
    @19
    @12
    @0
    @4
    @24
    @0
    @1
    @5
    @8
    simp1l
    #
    @2
    @3
    @4
    @8
    simp2r
    #
    cA
    cD
    xaddcl
    syl2anc
    adantr
    @12
    @10
    cxr
    wcel
    #
    @19
    @5
    @2
    @27
    @8
    cC
    cD
    xaddcl
    3ad2ant2
    #
    adantr
    @20
    @7
    @9
    @21
    clt
    wbr
    #
    @12
    @7
    @19
    @2
    @5
    @6
    @7
    simp3r
    #
    adantr
    @20
    @1
    @4
    @13
    @7
    @29
    wb
    @12
    @1
    @19
    @0
    @1
    @5
    @8
    simp1r
    #
    adantr
    @12
    @4
    @19
    @26
    adantr
    @12
    @13
    @16
    simprl
    cB
    cD
    cA
    xltadd2
    syl3anc
    mpbid
    @20
    @6
    @21
    @10
    clt
    wbr
    #
    @12
    @6
    @19
    @2
    @5
    @6
    @7
    simp3l
    #
    adantr
    @20
    @0
    @3
    @16
    @6
    @32
    wb
    @12
    @0
    @19
    @25
    adantr
    @12
    @3
    @19
    @2
    @3
    @4
    @8
    simp2l
    #
    adantr
    @12
    @13
    @16
    simprr
    cA
    cC
    cD
    xltadd1
    syl3anc
    mpbid
    xrlttrd
    anassrs
    @12
    @17
    @11
    @13
    @12
    @17
    wa
    @9
    cpnf
    @10
    clt
    @12
    @9
    cpnf
    clt
    wbr
    #
    @17
    @12
    @35
    @9
    cpnf
    wne
    #
    @12
    @0
    cA
    cpnf
    wne
    #
    @1
    cB
    cpnf
    wne
    #
    @36
    @25
    @12
    cA
    cpnf
    clt
    wbr
    #
    @37
    @12
    cA
    cC
    cpnf
    @25
    @34
    cpnf
    cxr
    wcel
    @12
    pnfxr
    a1i
    #
    @33
    @12
    @3
    cC
    cpnf
    cle
    wbr
    @34
    cC
    pnfge
    syl
    xrltletrd
    @12
    @0
    @39
    @37
    wb
    @25
    @0
    @39
    cA
    cpnf
    cA
    nltpnft
    necon2abid
    syl
    mpbid
    #
    @31
    @12
    cB
    cpnf
    clt
    wbr
    #
    @38
    @12
    cB
    cD
    cpnf
    @31
    @26
    @40
    @30
    @12
    @4
    cD
    cpnf
    cle
    wbr
    @26
    cD
    pnfge
    syl
    xrltletrd
    @12
    @1
    @42
    @38
    wb
    @31
    @1
    @42
    cB
    cpnf
    cB
    nltpnft
    necon2abid
    syl
    mpbid
    #
    cA
    cB
    xaddnepnf
    syl22anc
    @12
    @22
    @35
    @36
    wb
    @23
    @22
    @35
    @9
    cpnf
    @9
    nltpnft
    necon2abid
    syl
    mpbird
    adantr
    @17
    @12
    @10
    cC
    cpnf
    cxad
    co
    #
    cpnf
    cD
    cpnf
    cC
    cxad
    oveq2
    @12
    @3
    cC
    cmnf
    wne
    #
    @44
    cpnf
    wceq
    @34
    @12
    cmnf
    cC
    clt
    wbr
    #
    @45
    @12
    cmnf
    cA
    cC
    cmnf
    cxr
    wcel
    @12
    mnfxr
    a1i
    #
    @25
    @34
    @12
    @0
    cmnf
    cA
    cle
    wbr
    @25
    cA
    mnfle
    syl
    @33
    xrlelttrd
    @12
    @3
    @46
    @45
    wb
    @34
    @3
    @46
    cC
    cmnf
    cC
    ngtmnft
    necon2abid
    syl
    mpbid
    #
    cC
    xaddpnf1
    syl2anc
    sylan9eqr
    breqtrrd
    adantlr
    @12
    @18
    @11
    @13
    @12
    @18
    @11
    @12
    @11
    cD
    cmnf
    @12
    cD
    cmnf
    wne
    #
    @11
    wn
    #
    @12
    cmnf
    cD
    clt
    wbr
    #
    @49
    @12
    cmnf
    cB
    cD
    @47
    @31
    @26
    @12
    @1
    cmnf
    cB
    cle
    wbr
    @31
    cB
    mnfle
    syl
    @30
    xrlelttrd
    @12
    @4
    @51
    @49
    wb
    @26
    @4
    @51
    cD
    cmnf
    cD
    ngtmnft
    necon2abid
    syl
    mpbid
    #
    a1d
    necon4bd
    imp
    adantlr
    @12
    @16
    @17
    @18
    w3o
    #
    @13
    @12
    @4
    @53
    @26
    cD
    elxr
    sylib
    adantr
    mpjao3dan
    @12
    @14
    @11
    @12
    @11
    cA
    cpnf
    @12
    @37
    @50
    @41
    a1d
    necon4bd
    imp
    @12
    @15
    wa
    @9
    cmnf
    @10
    clt
    @15
    @12
    @9
    cmnf
    cB
    cxad
    co
    #
    cmnf
    cA
    cmnf
    cB
    cxad
    oveq1
    @12
    @1
    @38
    @54
    cmnf
    wceq
    @31
    @43
    cB
    xaddmnf2
    syl2anc
    sylan9eqr
    @12
    cmnf
    @10
    clt
    wbr
    #
    @15
    @12
    @55
    @10
    cmnf
    wne
    #
    @12
    @3
    @45
    @4
    @49
    @56
    @34
    @48
    @26
    @52
    cC
    cD
    xaddnemnf
    syl22anc
    @12
    @27
    @55
    @56
    wb
    @28
    @27
    @55
    @10
    cmnf
    @10
    ngtmnft
    necon2abid
    syl
    mpbird
    adantr
    eqbrtrd
    @12
    @0
    @13
    @14
    @15
    w3o
    @25
    cA
    elxr
    sylib
    mpjao3dan
    3expia
end
