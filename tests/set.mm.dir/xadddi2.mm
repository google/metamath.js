include "cxr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "clt.mm"
include "cxad.mm"
include "co.mm"
include "cxmu.mm"
include "wceq.mm"
include "cr.mm"
include "cpnf.mm"
include "cmnf.mm"
include "simpr.mm"
include "simp2l.mm"
include "ad2antrr.mm"
include "simp3l.mm"
include "xadddi.mm"
include "syl3anc.mm"
include "wne.mm"
include "pnfxr.mm"
include "adantr.mm"
include "xmulcl.mm"
include "sylancr.mm"
include "simpl3r.mm"
include "0lepnf.mm"
include "xmulge0.mm"
include "mpanl12.mm"
include "syl2anc.mm"
include "ge0nemnf.mm"
include "xaddpnf2.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "xmulpnf2.mm"
include "sylan.mm"
include "oveq1d.mm"
include "sylan9eqr.mm"
include "xaddcl.mm"
include "0xr.mm"
include "a1i.mm"
include "xaddid1.mm"
include "syl.mm"
include "xleadd2a.mm"
include "syl31anc.mm"
include "eqbrtrrd.mm"
include "xrltletrd.mm"
include "3eqtr4rd.mm"
include "mnfxr.mm"
include "cxne.mm"
include "xnegmnf.mm"
include "oveq1i.mm"
include "xmulneg1.mm"
include "syl5reqr.mm"
include "xnegpnf.mm"
include "eqeq12d.mm"
include "wb.mm"
include "xneg11.mm"
include "sylancl.mm"
include "bitr3d.mm"
include "necon3bid.mm"
include "mpbid.mm"
include "xaddmnf2.mm"
include "xmulmnf2.mm"
include "w3o.mm"
include "simpl1.mm"
include "elxr.mm"
include "sylib.mm"
include "mpjao3dan.mm"
include "simp1.mm"
include "xaddid2.mm"
include "oveq2.mm"
include "eqcomd.mm"
include "xmul01.mm"
include "3ad2ant1.mm"
include "oveq2d.mm"
include "wo.mm"
include "simp2r.mm"
include "xrleloe.mm"
include "mpjaodan.mm"

theorem xadddi2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR* /\ ( B e. RR* /\ 0 <_ B ) /\ ( C e. RR* /\ 0 <_ C ) ) -> ( A *e ( B +e C ) ) = ( ( A *e B ) +e ( A *e C ) ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cc0
    cB
    cle
    wbr
    #
    wa
    #
    cC
    cxr
    wcel
    #
    cc0
    cC
    cle
    wbr
    #
    wa
    #
    w3a
    #
    cc0
    cB
    clt
    wbr
    #
    cA
    cB
    cC
    cxad
    co
    #
    cxmu
    co
    #
    cA
    cB
    cxmu
    co
    #
    cA
    cC
    cxmu
    co
    #
    cxad
    co
    #
    wceq
    #
    cc0
    cB
    wceq
    #
    @7
    @8
    wa
    #
    cA
    cr
    wcel
    #
    @14
    cA
    cpnf
    wceq
    #
    cA
    cmnf
    wceq
    #
    @16
    @17
    wa
    @17
    @1
    @4
    @14
    @16
    @17
    simpr
    @7
    @1
    @8
    @17
    @0
    @1
    @2
    @6
    simp2l
    #
    ad2antrr
    @7
    @4
    @8
    @17
    @0
    @3
    @4
    @5
    simp3l
    #
    ad2antrr
    cA
    cB
    cC
    xadddi
    syl3anc
    @16
    @18
    wa
    #
    cpnf
    cpnf
    cC
    cxmu
    co
    #
    cxad
    co
    #
    cpnf
    @13
    @10
    @22
    @23
    cxr
    wcel
    #
    @23
    cmnf
    wne
    #
    @24
    cpnf
    wceq
    @22
    cpnf
    cxr
    wcel
    #
    @4
    @25
    pnfxr
    @16
    @4
    @18
    @7
    @4
    @8
    @21
    adantr
    #
    adantr
    cpnf
    cC
    xmulcl
    #
    sylancr
    @16
    @26
    @18
    @16
    @25
    cc0
    @23
    cle
    wbr
    #
    @26
    @16
    @27
    @4
    @25
    pnfxr
    @28
    @29
    sylancr
    @16
    @4
    @5
    @30
    @28
    @4
    @5
    @0
    @3
    @8
    simpl3r
    #
    @27
    cc0
    cpnf
    cle
    wbr
    @6
    @30
    pnfxr
    0lepnf
    cpnf
    cC
    xmulge0
    mpanl12
    syl2anc
    @23
    ge0nemnf
    syl2anc
    #
    adantr
    @23
    xaddpnf2
    syl2anc
    @18
    @16
    @13
    cpnf
    cB
    cxmu
    co
    #
    @23
    cxad
    co
    @24
    @18
    @11
    @33
    @12
    @23
    cxad
    cA
    cpnf
    cB
    cxmu
    oveq1
    cA
    cpnf
    cC
    cxmu
    oveq1
    oveq12d
    @16
    @33
    cpnf
    @23
    cxad
    @7
    @1
    @8
    @33
    cpnf
    wceq
    @20
    cB
    xmulpnf2
    sylan
    oveq1d
    sylan9eqr
    @18
    @16
    @10
    cpnf
    @9
    cxmu
    co
    #
    cpnf
    cA
    cpnf
    @9
    cxmu
    oveq1
    @16
    @9
    cxr
    wcel
    #
    cc0
    @9
    clt
    wbr
    #
    @34
    cpnf
    wceq
    @7
    @35
    @8
    @7
    @1
    @4
    @35
    @20
    @21
    cB
    cC
    xaddcl
    syl2anc
    adantr
    #
    @16
    cc0
    cB
    @9
    cc0
    cxr
    wcel
    #
    @16
    0xr
    a1i
    #
    @7
    @1
    @8
    @20
    adantr
    #
    @37
    @7
    @8
    simpr
    @16
    cB
    cc0
    cxad
    co
    #
    cB
    @9
    cle
    @16
    @1
    @41
    cB
    wceq
    @40
    cB
    xaddid1
    syl
    @16
    @38
    @4
    @1
    @5
    @41
    @9
    cle
    wbr
    @39
    @28
    @40
    @31
    cc0
    cC
    cB
    xleadd2a
    syl31anc
    eqbrtrrd
    xrltletrd
    #
    @9
    xmulpnf2
    syl2anc
    sylan9eqr
    3eqtr4rd
    @16
    @19
    wa
    cmnf
    cmnf
    cC
    cxmu
    co
    #
    cxad
    co
    #
    cmnf
    @13
    @10
    @16
    @44
    cmnf
    wceq
    #
    @19
    @16
    @43
    cxr
    wcel
    #
    @43
    cpnf
    wne
    #
    @45
    @16
    cmnf
    cxr
    wcel
    #
    @4
    @46
    mnfxr
    @28
    cmnf
    cC
    xmulcl
    sylancr
    #
    @16
    @26
    @47
    @32
    @16
    @23
    cmnf
    @43
    cpnf
    @16
    @43
    cxne
    #
    cpnf
    cxne
    #
    wceq
    #
    @23
    cmnf
    wceq
    @43
    cpnf
    wceq
    #
    @16
    @50
    @23
    @51
    cmnf
    @16
    @23
    cmnf
    cxne
    #
    cC
    cxmu
    co
    #
    @50
    @54
    cpnf
    cC
    cxmu
    xnegmnf
    oveq1i
    @16
    @48
    @4
    @55
    @50
    wceq
    mnfxr
    @28
    cmnf
    cC
    xmulneg1
    sylancr
    syl5reqr
    @51
    cmnf
    wceq
    @16
    xnegpnf
    a1i
    eqeq12d
    @16
    @46
    @27
    @52
    @53
    wb
    @49
    pnfxr
    @43
    cpnf
    xneg11
    sylancl
    bitr3d
    necon3bid
    mpbid
    @43
    xaddmnf2
    syl2anc
    adantr
    @19
    @16
    @13
    cmnf
    cB
    cxmu
    co
    #
    @43
    cxad
    co
    @44
    @19
    @11
    @56
    @12
    @43
    cxad
    cA
    cmnf
    cB
    cxmu
    oveq1
    cA
    cmnf
    cC
    cxmu
    oveq1
    oveq12d
    @16
    @56
    cmnf
    @43
    cxad
    @7
    @1
    @8
    @56
    cmnf
    wceq
    @20
    cB
    xmulmnf2
    sylan
    oveq1d
    sylan9eqr
    @19
    @16
    @10
    cmnf
    @9
    cxmu
    co
    #
    cmnf
    cA
    cmnf
    @9
    cxmu
    oveq1
    @16
    @35
    @36
    @57
    cmnf
    wceq
    @37
    @42
    @9
    xmulmnf2
    syl2anc
    sylan9eqr
    3eqtr4rd
    @16
    @0
    @17
    @18
    @19
    w3o
    @0
    @3
    @6
    @8
    simpl1
    cA
    elxr
    sylib
    mpjao3dan
    @7
    @15
    wa
    #
    cc0
    @12
    cxad
    co
    #
    @12
    @13
    @10
    @58
    @12
    cxr
    wcel
    #
    @59
    @12
    wceq
    @7
    @60
    @15
    @7
    @0
    @4
    @60
    @0
    @3
    @6
    simp1
    @21
    cA
    cC
    xmulcl
    syl2anc
    adantr
    @12
    xaddid2
    syl
    @58
    @11
    cc0
    @12
    cxad
    @15
    @7
    @11
    cA
    cc0
    cxmu
    co
    #
    cc0
    @15
    @61
    @11
    cc0
    cB
    cA
    cxmu
    oveq2
    eqcomd
    @0
    @3
    @61
    cc0
    wceq
    @6
    cA
    xmul01
    3ad2ant1
    sylan9eqr
    oveq1d
    @58
    @9
    cC
    cA
    cxmu
    @15
    @7
    @9
    cc0
    cC
    cxad
    co
    #
    cC
    @15
    @62
    @9
    cc0
    cB
    cC
    cxad
    oveq1
    eqcomd
    @7
    @4
    @62
    cC
    wceq
    @21
    cC
    xaddid2
    syl
    sylan9eqr
    oveq2d
    3eqtr4rd
    @7
    @2
    @8
    @15
    wo
    #
    @0
    @1
    @2
    @6
    simp2r
    @7
    @38
    @1
    @2
    @63
    wb
    0xr
    @20
    cc0
    cB
    xrleloe
    sylancr
    mpbid
    mpjaodan
end
