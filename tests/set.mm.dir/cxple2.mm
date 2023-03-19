include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "crp.mm"
include "w3a.mm"
include "clt.mm"
include "ccxp.mm"
include "co.mm"
include "wb.mm"
include "wceq.mm"
include "simpl1l.mm"
include "simpr.mm"
include "elrpd.mm"
include "adantr.mm"
include "simp2l.mm"
include "ad2antrr.mm"
include "simp3.mm"
include "clog.mm"
include "cfv.mm"
include "cmul.mm"
include "ce.mm"
include "rpred.mm"
include "relogcl.mm"
include "3ad2ant1.mm"
include "remulcld.mm"
include "3ad2ant2.mm"
include "efle.mm"
include "syl2anc.mm"
include "lemul2d.mm"
include "reeflog.mm"
include "breq12d.mm"
include "3bitr3rd.mm"
include "cc.mm"
include "wne.mm"
include "rpre.mm"
include "recnd.mm"
include "rpne0.mm"
include "cxpef.mm"
include "syl3anc.mm"
include "3bitr4d.mm"
include "wn.mm"
include "0re.mm"
include "simp1l.mm"
include "ltnle.mm"
include "sylancr.mm"
include "biimpa.mm"
include "rpcxpcl.mm"
include "rpgt0.mm"
include "mpbid.mm"
include "syl.mm"
include "rpne0d.mm"
include "0cxp.mm"
include "breq2d.mm"
include "mtbird.mm"
include "2falsed.mm"
include "breq2.mm"
include "oveq1.mm"
include "bibi12d.mm"
include "syl5ibcom.mm"
include "imp.mm"
include "wo.mm"
include "simp2r.mm"
include "leloe.mm"
include "mpjaodan.mm"
include "simpl2r.mm"
include "eqbrtrrd.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "simpl2l.mm"
include "cxpge0.mm"
include "2thd.mm"
include "simp1r.mm"

theorem cxple2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. RR /\ 0 <_ A ) /\ ( B e. RR /\ 0 <_ B ) /\ C e. RR+ ) -> ( A <_ B <-> ( A ^c C ) <_ ( B ^c C ) ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    cB
    cr
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
    crp
    wcel
    #
    w3a
    #
    cc0
    cA
    clt
    wbr
    #
    cA
    cB
    cle
    wbr
    #
    cA
    cC
    ccxp
    co
    #
    cB
    cC
    ccxp
    co
    #
    cle
    wbr
    #
    wb
    #
    cc0
    cA
    wceq
    #
    @7
    @8
    wa
    #
    cc0
    cB
    clt
    wbr
    #
    @13
    cc0
    cB
    wceq
    #
    @15
    @16
    wa
    #
    cA
    crp
    wcel
    #
    cB
    crp
    wcel
    #
    @6
    @13
    @15
    @19
    @16
    @15
    cA
    @0
    @1
    @5
    @6
    @8
    simpl1l
    @7
    @8
    simpr
    elrpd
    #
    adantr
    @18
    cB
    @7
    @3
    @8
    @16
    @2
    @3
    @4
    @6
    simp2l
    #
    ad2antrr
    @15
    @16
    simpr
    elrpd
    @7
    @6
    @8
    @16
    @2
    @5
    @6
    simp3
    #
    ad2antrr
    @19
    @20
    @6
    w3a
    #
    cC
    cA
    clog
    cfv
    #
    cmul
    co
    #
    cC
    cB
    clog
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    @26
    ce
    cfv
    #
    @28
    ce
    cfv
    #
    cle
    wbr
    #
    @9
    @12
    @24
    @26
    cr
    wcel
    @28
    cr
    wcel
    @29
    @32
    wb
    @24
    cC
    @25
    @24
    cC
    @19
    @20
    @6
    simp3
    #
    rpred
    #
    @19
    @20
    @25
    cr
    wcel
    #
    @6
    cA
    relogcl
    3ad2ant1
    #
    remulcld
    @24
    cC
    @27
    @34
    @20
    @19
    @27
    cr
    wcel
    #
    @6
    cB
    relogcl
    3ad2ant2
    #
    remulcld
    @26
    @28
    efle
    syl2anc
    @24
    @25
    @27
    cle
    wbr
    #
    @25
    ce
    cfv
    #
    @27
    ce
    cfv
    #
    cle
    wbr
    #
    @29
    @9
    @24
    @35
    @37
    @39
    @42
    wb
    @36
    @38
    @25
    @27
    efle
    syl2anc
    @24
    @25
    @27
    cC
    @36
    @38
    @33
    lemul2d
    @24
    @40
    cA
    @41
    cB
    cle
    @19
    @20
    @40
    cA
    wceq
    @6
    cA
    reeflog
    3ad2ant1
    @20
    @19
    @41
    cB
    wceq
    @6
    cB
    reeflog
    3ad2ant2
    breq12d
    3bitr3rd
    @24
    @10
    @30
    @11
    @31
    cle
    @24
    cA
    cc
    wcel
    cA
    cc0
    wne
    #
    cC
    cc
    wcel
    #
    @10
    @30
    wceq
    @24
    cA
    @19
    @20
    @0
    @6
    cA
    rpre
    3ad2ant1
    recnd
    @19
    @20
    @43
    @6
    cA
    rpne0
    3ad2ant1
    @24
    cC
    @34
    recnd
    #
    cA
    cC
    cxpef
    syl3anc
    @24
    cB
    cc
    wcel
    cB
    cc0
    wne
    #
    @44
    @11
    @31
    wceq
    @24
    cB
    @20
    @19
    @3
    @6
    cB
    rpre
    3ad2ant2
    recnd
    @20
    @19
    @46
    @6
    cB
    rpne0
    3ad2ant2
    @45
    cB
    cC
    cxpef
    syl3anc
    breq12d
    3bitr4d
    syl3anc
    @15
    @17
    @13
    @15
    cA
    cc0
    cle
    wbr
    #
    @10
    cc0
    cC
    ccxp
    co
    #
    cle
    wbr
    #
    wb
    @17
    @13
    @15
    @47
    @49
    @7
    @8
    @47
    wn
    #
    @7
    cc0
    cr
    wcel
    #
    @0
    @8
    @50
    wb
    0re
    @0
    @1
    @5
    @6
    simp1l
    #
    cc0
    cA
    ltnle
    sylancr
    biimpa
    @15
    @49
    @10
    cc0
    cle
    wbr
    #
    @15
    @10
    crp
    wcel
    #
    @53
    wn
    #
    @15
    @19
    cC
    cr
    wcel
    #
    @54
    @21
    @7
    @56
    @8
    @7
    cC
    @23
    rpred
    #
    adantr
    cA
    cC
    rpcxpcl
    syl2anc
    @54
    cc0
    @10
    clt
    wbr
    #
    @55
    @10
    rpgt0
    @54
    @51
    @10
    cr
    wcel
    @58
    @55
    wb
    0re
    @10
    rpre
    cc0
    @10
    ltnle
    sylancr
    mpbid
    syl
    @15
    @48
    cc0
    @10
    cle
    @7
    @48
    cc0
    wceq
    #
    @8
    @7
    @44
    cC
    cc0
    wne
    @59
    @7
    cC
    @57
    recnd
    @7
    cC
    @23
    rpne0d
    cC
    0cxp
    syl2anc
    #
    adantr
    breq2d
    mtbird
    2falsed
    @17
    @47
    @9
    @49
    @12
    cc0
    cB
    cA
    cle
    breq2
    @17
    @48
    @11
    @10
    cle
    cc0
    cB
    cC
    ccxp
    oveq1
    breq2d
    bibi12d
    syl5ibcom
    imp
    @7
    @16
    @17
    wo
    #
    @8
    @7
    @4
    @61
    @2
    @3
    @4
    @6
    simp2r
    @7
    @51
    @3
    @4
    @61
    wb
    0re
    @22
    cc0
    cB
    leloe
    sylancr
    mpbid
    adantr
    mpjaodan
    @7
    @14
    wa
    #
    @9
    @12
    @62
    cc0
    cA
    cB
    cle
    @7
    @14
    simpr
    #
    @3
    @4
    @2
    @6
    @14
    simpl2r
    #
    eqbrtrrd
    @62
    cc0
    @10
    @11
    cle
    @62
    @48
    cc0
    @10
    @7
    @59
    @14
    @60
    adantr
    @62
    cc0
    cA
    cC
    ccxp
    @63
    oveq1d
    eqtr3d
    @62
    @3
    @4
    @56
    cc0
    @11
    cle
    wbr
    @3
    @4
    @2
    @6
    @14
    simpl2l
    @64
    @7
    @56
    @14
    @57
    adantr
    cB
    cC
    cxpge0
    syl3anc
    eqbrtrrd
    2thd
    @7
    @1
    @8
    @14
    wo
    #
    @0
    @1
    @5
    @6
    simp1r
    @7
    @51
    @0
    @1
    @65
    wb
    0re
    @52
    cc0
    cA
    leloe
    sylancr
    mpbid
    mpjaodan
end
