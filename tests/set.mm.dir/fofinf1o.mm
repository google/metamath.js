include "wfo.mm"
include "cen.mm"
include "wbr.mm"
include "cfn.mm"
include "wcel.mm"
include "w3a.mm"
include "wf1.mm"
include "wf1o.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "simp1.mm"
include "fof.mm"
include "syl.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "cdom.mm"
include "wn.mm"
include "csdm.mm"
include "domnsym.mm"
include "wpss.mm"
include "simp3.mm"
include "simp2.mm"
include "enfii.mm"
include "syl2anc.mm"
include "ad2antrr.mm"
include "wss.mm"
include "wne.mm"
include "difssd.mm"
include "simplrr.mm"
include "neldifsn.mm"
include "nelne1.mm"
include "sylancl.mm"
include "necomd.mm"
include "df-pss.mm"
include "sylanbrc.mm"
include "php3.mm"
include "sdomentr.mm"
include "nsyl3.mm"
include "cres.mm"
include "adantr.mm"
include "difss.mm"
include "ssfi.mm"
include "wrex.mm"
include "fssres.mm"
include "foelrn.mm"
include "sylan.mm"
include "simprll.mm"
include "simprrr.mm"
include "eldifsn.mm"
include "simprrl.mm"
include "eqcomd.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "syl5ibrcom.mm"
include "imp.mm"
include "eqid.mm"
include "mpan2.mm"
include "sylbir.mm"
include "adantll.mm"
include "pm2.61dane.mm"
include "fvres.mm"
include "rexbiia.mm"
include "eqeq1.mm"
include "syl5bb.mm"
include "rexlimdva.mm"
include "syldan.mm"
include "ralrimiva.mm"
include "dffo3.mm"
include "fodomfi.mm"
include "anassrs.mm"
include "expr.mm"
include "necon1bd.mm"
include "mpd.mm"
include "ex.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "df-f1o.mm"

theorem fofinf1o
  let cA: class A
  let cB: class B
  let cF: class F
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( F : A -onto-> B /\ A ~~ B /\ B e. Fin ) -> F : A -1-1-onto-> B )

  proof
    cA
    cB
    cF
    wfo
    #
    cA
    cB
    cen
    wbr
    #
    cB
    cfn
    wcel
    #
    w3a
    #
    cA
    cB
    cF
    wf1
    #
    @0
    cA
    cB
    cF
    wf1o
    @3
    cA
    cB
    cF
    wf
    #
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    cA
    wral
    vx
    cA
    wral
    @4
    @3
    @0
    @5
    @0
    @1
    @2
    simp1
    #
    cA
    cB
    cF
    fof
    syl
    #
    @3
    @12
    vx
    vy
    cA
    cA
    @3
    @6
    cA
    wcel
    #
    @8
    cA
    wcel
    #
    wa
    #
    wa
    #
    @10
    @11
    @18
    @10
    wa
    #
    cB
    cA
    @8
    csn
    #
    cdif
    #
    cdom
    wbr
    #
    wn
    @11
    @22
    @21
    cB
    csdm
    wbr
    #
    @19
    cB
    @21
    domnsym
    @19
    @21
    cA
    csdm
    wbr
    #
    @1
    @23
    @19
    cA
    cfn
    wcel
    #
    @21
    cA
    wpss
    #
    @24
    @3
    @25
    @17
    @10
    @3
    @2
    @1
    @25
    @0
    @1
    @2
    simp3
    @0
    @1
    @2
    simp2
    #
    cA
    cB
    enfii
    syl2anc
    #
    ad2antrr
    @19
    @21
    cA
    wss
    #
    @21
    cA
    wne
    @26
    @19
    cA
    @20
    difssd
    @19
    cA
    @21
    @19
    @16
    @8
    @21
    wcel
    wn
    cA
    @21
    wne
    @3
    @15
    @16
    @10
    simplrr
    @8
    cA
    neldifsn
    @8
    cA
    @21
    nelne1
    sylancl
    necomd
    @21
    cA
    df-pss
    sylanbrc
    cA
    @21
    php3
    syl2anc
    @3
    @1
    @17
    @10
    @27
    ad2antrr
    @21
    cA
    cB
    sdomentr
    syl2anc
    nsyl3
    @19
    @22
    @6
    @8
    @18
    @10
    @6
    @8
    wne
    #
    @22
    @3
    @17
    @10
    @30
    wa
    #
    @22
    @3
    @17
    @31
    wa
    #
    wa
    #
    @21
    cfn
    wcel
    #
    @21
    cB
    cF
    @21
    cres
    #
    wfo
    #
    @22
    @33
    @25
    @29
    @34
    @3
    @25
    @32
    @28
    adantr
    cA
    @20
    difss
    #
    cA
    @21
    ssfi
    sylancl
    @33
    @21
    cB
    @35
    wf
    #
    vz
    cv
    #
    vw
    cv
    #
    @35
    cfv
    #
    wceq
    #
    vw
    @21
    wrex
    #
    vz
    cB
    wral
    @36
    @33
    @5
    @29
    @38
    @3
    @5
    @32
    @14
    adantr
    @37
    cA
    cB
    @21
    cF
    fssres
    sylancl
    @33
    @43
    vz
    cB
    @33
    @39
    cB
    wcel
    #
    @39
    vu
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vu
    cA
    wrex
    #
    @43
    @33
    @0
    @44
    @48
    @3
    @0
    @32
    @13
    adantr
    vu
    cA
    cB
    @39
    cF
    foelrn
    sylan
    @33
    @48
    @43
    @33
    @47
    @43
    vu
    cA
    @33
    @45
    cA
    wcel
    #
    wa
    #
    @43
    @47
    @46
    @40
    cF
    cfv
    #
    wceq
    #
    vw
    @21
    wrex
    #
    @50
    @53
    @45
    @8
    @50
    vu
    vy
    weq
    #
    @53
    @33
    @54
    @53
    wi
    @49
    @33
    @53
    @54
    @9
    @51
    wceq
    #
    vw
    @21
    wrex
    #
    @33
    @6
    @21
    wcel
    #
    @9
    @7
    wceq
    #
    @56
    @33
    @15
    @30
    @57
    @3
    @15
    @16
    @31
    simprll
    @3
    @17
    @10
    @30
    simprrr
    @6
    cA
    @8
    eldifsn
    sylanbrc
    @33
    @7
    @9
    @3
    @17
    @10
    @30
    simprrl
    eqcomd
    @55
    @58
    vw
    @6
    @21
    vw
    vx
    weq
    @51
    @7
    @9
    @40
    @6
    cF
    fveq2
    eqeq2d
    rspcev
    syl2anc
    @54
    @52
    @55
    vw
    @21
    @54
    @46
    @9
    @51
    @45
    @8
    cF
    fveq2
    eqeq1d
    rexbidv
    syl5ibrcom
    adantr
    imp
    @49
    @45
    @8
    wne
    #
    @53
    @33
    @49
    @59
    wa
    @45
    @21
    wcel
    #
    @53
    @45
    cA
    @8
    eldifsn
    @60
    @46
    @46
    wceq
    #
    @53
    @46
    eqid
    @52
    @61
    vw
    @45
    @21
    vw
    vu
    weq
    @51
    @46
    @46
    @40
    @45
    cF
    fveq2
    eqeq2d
    rspcev
    mpan2
    sylbir
    adantll
    pm2.61dane
    @43
    @39
    @51
    wceq
    #
    vw
    @21
    wrex
    @47
    @53
    @42
    @62
    vw
    @21
    @40
    @21
    wcel
    @41
    @51
    @39
    @40
    @21
    cF
    fvres
    eqeq2d
    rexbiia
    @47
    @62
    @52
    vw
    @21
    @39
    @46
    @51
    eqeq1
    rexbidv
    syl5bb
    syl5ibrcom
    rexlimdva
    imp
    syldan
    ralrimiva
    vw
    vz
    @21
    cB
    @35
    dffo3
    sylanbrc
    @21
    cB
    @35
    fodomfi
    syl2anc
    anassrs
    expr
    necon1bd
    mpd
    ex
    ralrimivva
    vx
    vy
    cA
    cB
    cF
    dff13
    sylanbrc
    @13
    cA
    cB
    cF
    df-f1o
    sylanbrc
end
