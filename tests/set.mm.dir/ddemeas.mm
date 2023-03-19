include "cdde.mm"
include "cr.mm"
include "cpw.mm"
include "cmeas.mm"
include "cfv.mm"
include "wcel.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wdisj.mm"
include "wa.mm"
include "cuni.mm"
include "cesum.mm"
include "wi.mm"
include "wral.mm"
include "c1.mm"
include "cif.mm"
include "cxr.mm"
include "cle.mm"
include "1re.mm"
include "rexri.mm"
include "0le1.mm"
include "pnfge.mm"
include "ax-mp.mm"
include "w3a.mm"
include "wb.mm"
include "0xr.mm"
include "pnfxr.mm"
include "elicc1.mm"
include "mp2an.mm"
include "mpbir3an.mm"
include "0e0iccpnf.mm"
include "keepel.mm"
include "rgenw.mm"
include "df-dde.mm"
include "fmpt.mm"
include "mpbi.mm"
include "wss.mm"
include "wn.mm"
include "0ss.mm"
include "noel.mm"
include "ddeval0.mm"
include "crab.mm"
include "cxad.mm"
include "cun.mm"
include "rabxm.mm"
include "esumeq1.mm"
include "nfv.mm"
include "nfcv.mm"
include "rabexg.mm"
include "cin.mm"
include "rabnc.mm"
include "a1i.mm"
include "elrabi.mm"
include "adantl.mm"
include "simpl.mm"
include "elelpwi.mm"
include "syl2anc.mm"
include "ffvelrni.mm"
include "syl.mm"
include "esumsplit.mm"
include "syl5eq.mm"
include "adantr.mm"
include "wrex.mm"
include "csn.mm"
include "simp-4l.mm"
include "vex.mm"
include "rabsnel.mm"
include "eleq2.mm"
include "rabsnt.mm"
include "ancoms.mm"
include "adantrr.mm"
include "cvv.mm"
include "simpr.mm"
include "fveq2d.mm"
include "esumsn.mm"
include "elpwid.mm"
include "simprr.mm"
include "ddeval1.mm"
include "eqtrd.mm"
include "syl12anc.mm"
include "wex.mm"
include "wreu.mm"
include "wrmo.mm"
include "wal.mm"
include "df-disj.mm"
include "c0ex.mm"
include "eleq1.mm"
include "rmobidv.mm"
include "spcv.mm"
include "sylbi.mm"
include "rmo5.mm"
include "biimpi.mm"
include "imp.mm"
include "sylan.mm"
include "reusn.mm"
include "sylib.mm"
include "cbvrabv.mm"
include "eqeq1i.mm"
include "ancri.mm"
include "sylbir.mm"
include "eximi.mm"
include "df-rex.mm"
include "sylibr.mm"
include "adantll.mm"
include "r19.29a.mm"
include "elpwi.mm"
include "sspwuni.mm"
include "eluni2.mm"
include "biimpri.mm"
include "syl2an.mm"
include "adantlr.mm"
include "eqtr4d.mm"
include "nfre1.mm"
include "nfn.mm"
include "elrab.mm"
include "exbii.mm"
include "neq0.mm"
include "3bitr4i.mm"
include "con1i.mm"
include "esumeq1d.mm"
include "esumnul.mm"
include "syl6eq.mm"
include "con3i.mm"
include "pm2.61dan.mm"
include "notbid.mm"
include "simprbi.mm"
include "esumeq2dv.mm"
include "rabex.mm"
include "esum0.mm"
include "oveq12d.mm"
include "vuniex.mm"
include "elpw.mm"
include "iccssxr.mm"
include "sseldi.mm"
include "xaddid1.mm"
include "4syl.mm"
include "3eqtrrd.mm"
include "adantrl.mm"
include "ex.mm"
include "rgen.mm"
include "csiga.mm"
include "crn.mm"
include "reex.mm"
include "pwsiga.mm"
include "elrnsiga.mm"
include "ismeas.mm"
include "mp2b.mm"

theorem ddemeas
  let va: setvar a
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y


  assert |- Ddelta e. ( measures ` ~P RR )

  proof
    cdde
    cr
    cpw
    #
    cmeas
    cfv
    wcel
    #
    @0
    cc0
    cpnf
    cicc
    co
    #
    cdde
    wf
    #
    c0
    cdde
    cfv
    cc0
    wceq
    #
    vx
    cv
    #
    com
    cdom
    wbr
    #
    vy
    @5
    vy
    cv
    #
    wdisj
    #
    wa
    #
    @5
    cuni
    #
    cdde
    cfv
    #
    @5
    @7
    cdde
    cfv
    #
    vy
    cesum
    #
    wceq
    #
    wi
    #
    vx
    @0
    cpw
    #
    wral
    #
    cc0
    va
    cv
    #
    wcel
    #
    c1
    cc0
    cif
    #
    @2
    wcel
    #
    va
    @0
    wral
    @3
    @21
    va
    @0
    @19
    c1
    cc0
    @2
    c1
    @2
    wcel
    #
    c1
    cxr
    wcel
    #
    cc0
    c1
    cle
    wbr
    #
    c1
    cpnf
    cle
    wbr
    #
    c1
    1re
    rexri
    #
    0le1
    @23
    @25
    @26
    c1
    pnfge
    ax-mp
    cc0
    cxr
    wcel
    cpnf
    cxr
    wcel
    @22
    @23
    @24
    @25
    w3a
    wb
    0xr
    pnfxr
    cc0
    cpnf
    c1
    elicc1
    mp2an
    mpbir3an
    0e0iccpnf
    keepel
    rgenw
    va
    @0
    @2
    @20
    cdde
    va
    df-dde
    fmpt
    mpbi
    #
    c0
    cr
    wss
    cc0
    c0
    wcel
    wn
    @4
    cr
    0ss
    cc0
    noel
    c0
    ddeval0
    mp2an
    @15
    vx
    @16
    @5
    @16
    wcel
    #
    @9
    @14
    @28
    @8
    @14
    @6
    @28
    @8
    wa
    #
    @13
    @19
    va
    @5
    crab
    #
    @12
    vy
    cesum
    #
    @19
    wn
    #
    va
    @5
    crab
    #
    @12
    vy
    cesum
    #
    cxad
    co
    #
    @11
    cc0
    cxad
    co
    #
    @11
    @28
    @13
    @35
    wceq
    @8
    @28
    @13
    @30
    @33
    cun
    #
    @12
    vy
    cesum
    #
    @35
    @5
    @37
    wceq
    @13
    @38
    wceq
    @19
    va
    @5
    rabxm
    @5
    @37
    @12
    vy
    esumeq1
    ax-mp
    @28
    @30
    @33
    @12
    vy
    @28
    vy
    nfv
    vy
    @30
    nfcv
    vy
    @33
    nfcv
    #
    @19
    va
    @5
    @16
    rabexg
    @32
    va
    @5
    @16
    rabexg
    @30
    @33
    cin
    c0
    wceq
    @28
    @19
    va
    @5
    rabnc
    a1i
    @28
    @7
    @30
    wcel
    #
    wa
    #
    @7
    @0
    wcel
    #
    @12
    @2
    wcel
    #
    @41
    @7
    @5
    wcel
    #
    @28
    @42
    @40
    @44
    @28
    @19
    va
    @7
    @5
    elrabi
    adantl
    @28
    @40
    simpl
    @7
    @5
    @0
    elelpwi
    #
    syl2anc
    @0
    @2
    @7
    cdde
    @27
    ffvelrni
    #
    syl
    @28
    @7
    @33
    wcel
    #
    wa
    #
    @42
    @43
    @48
    @44
    @28
    @42
    @47
    @44
    @28
    @32
    va
    @7
    @5
    elrabi
    adantl
    @28
    @47
    simpl
    @45
    syl2anc
    #
    @46
    syl
    esumsplit
    syl5eq
    adantr
    @29
    @31
    @11
    @34
    cc0
    cxad
    @29
    cc0
    @7
    wcel
    #
    vy
    @5
    wrex
    #
    @31
    @11
    wceq
    @29
    @51
    wa
    #
    @31
    c1
    @11
    @52
    @30
    vk
    cv
    #
    csn
    #
    wceq
    #
    @31
    c1
    wceq
    vk
    @5
    @52
    @53
    @5
    wcel
    #
    wa
    #
    @55
    wa
    #
    @31
    @54
    @12
    vy
    cesum
    #
    c1
    @55
    @31
    @59
    wceq
    @57
    @30
    @54
    @12
    vy
    esumeq1
    adantl
    @58
    @28
    @56
    cc0
    @53
    wcel
    #
    @59
    c1
    wceq
    @28
    @8
    @51
    @56
    @55
    simp-4l
    @55
    @56
    @57
    @19
    va
    @5
    @53
    vk
    vex
    #
    rabsnel
    #
    adantl
    @55
    @60
    @57
    @19
    @60
    va
    @5
    @53
    @61
    @18
    @53
    cc0
    eleq2
    rabsnt
    adantl
    @28
    @56
    @60
    wa
    wa
    #
    @59
    @53
    cdde
    cfv
    #
    c1
    @63
    @53
    @0
    wcel
    #
    @59
    @64
    wceq
    @28
    @56
    @65
    @60
    @56
    @28
    @65
    @53
    @5
    @0
    elelpwi
    ancoms
    adantrr
    #
    @65
    @12
    @64
    vy
    @53
    cvv
    @65
    @7
    @53
    wceq
    #
    wa
    @7
    @53
    cdde
    @65
    @67
    simpr
    fveq2d
    @53
    cvv
    wcel
    @65
    @61
    a1i
    @0
    @2
    @53
    cdde
    @27
    ffvelrni
    esumsn
    syl
    @63
    @53
    cr
    wss
    @60
    @64
    c1
    wceq
    @63
    @53
    cr
    @66
    elpwid
    @28
    @56
    @60
    simprr
    @53
    ddeval1
    syl2anc
    eqtrd
    syl12anc
    eqtrd
    @8
    @51
    @55
    vk
    @5
    wrex
    #
    @28
    @8
    @51
    wa
    #
    @50
    vy
    @5
    crab
    #
    @54
    wceq
    #
    vk
    wex
    #
    @68
    @69
    @50
    vy
    @5
    wreu
    #
    @72
    @8
    @50
    vy
    @5
    wrmo
    #
    @51
    @73
    @8
    @53
    @7
    wcel
    #
    vy
    @5
    wrmo
    #
    vk
    wal
    @74
    vy
    vk
    @5
    @7
    df-disj
    @76
    @74
    vk
    cc0
    c0ex
    @53
    cc0
    wceq
    @75
    @50
    vy
    @5
    @53
    cc0
    @7
    eleq1
    rmobidv
    spcv
    sylbi
    @74
    @51
    @73
    @74
    @51
    @73
    wi
    @50
    vy
    @5
    rmo5
    biimpi
    imp
    sylan
    @50
    vy
    vk
    @5
    reusn
    sylib
    @72
    @56
    @55
    wa
    #
    vk
    wex
    @68
    @71
    @77
    vk
    @71
    @55
    @77
    @30
    @70
    @54
    @19
    @50
    va
    vy
    @5
    @18
    @7
    cc0
    eleq2
    #
    cbvrabv
    eqeq1i
    @55
    @56
    @62
    ancri
    sylbir
    eximi
    @55
    vk
    @5
    df-rex
    sylibr
    syl
    adantll
    r19.29a
    @28
    @51
    @11
    c1
    wceq
    #
    @8
    @28
    @10
    cr
    wss
    #
    cc0
    @10
    wcel
    #
    @79
    @51
    @28
    @5
    @0
    wss
    @80
    @5
    @0
    elpwi
    @5
    cr
    sspwuni
    sylib
    #
    @81
    @51
    vy
    cc0
    @5
    eluni2
    #
    biimpri
    @10
    ddeval1
    syl2an
    adantlr
    eqtr4d
    @29
    @51
    wn
    #
    wa
    @31
    cc0
    @11
    @84
    @31
    cc0
    wceq
    @29
    @84
    @31
    c0
    @12
    vy
    cesum
    cc0
    @84
    @30
    c0
    @12
    vy
    @51
    vy
    @50
    vy
    @5
    nfre1
    nfn
    @30
    c0
    wceq
    #
    @51
    @85
    wn
    #
    @51
    @40
    vy
    wex
    @44
    @50
    wa
    #
    vy
    wex
    @86
    @51
    @40
    @87
    vy
    @19
    @50
    va
    @7
    @5
    @78
    elrab
    exbii
    vy
    @30
    neq0
    @50
    vy
    @5
    df-rex
    3bitr4i
    biimpi
    con1i
    esumeq1d
    vy
    @12
    esumnul
    syl6eq
    adantl
    @28
    @84
    @11
    cc0
    wceq
    #
    @8
    @28
    @80
    @81
    wn
    @88
    @84
    @82
    @81
    @51
    @81
    @51
    @83
    biimpi
    con3i
    @10
    ddeval0
    syl2an
    adantlr
    eqtr4d
    pm2.61dan
    @28
    @34
    cc0
    wceq
    @8
    @28
    @34
    @33
    cc0
    vy
    cesum
    #
    cc0
    @28
    @33
    @12
    cc0
    vy
    @48
    @7
    cr
    wss
    @50
    wn
    #
    @12
    cc0
    wceq
    @48
    @7
    cr
    @49
    elpwid
    @47
    @90
    @28
    @47
    @44
    @90
    @32
    @90
    va
    @7
    @5
    @18
    @7
    wceq
    @19
    @50
    @78
    notbid
    elrab
    simprbi
    adantl
    @7
    ddeval0
    syl2anc
    esumeq2dv
    @33
    cvv
    wcel
    @89
    cc0
    wceq
    @32
    va
    @5
    vx
    vex
    rabex
    @33
    vy
    cvv
    @39
    esum0
    ax-mp
    syl6eq
    adantr
    oveq12d
    @28
    @36
    @11
    wceq
    #
    @8
    @28
    @80
    @10
    @0
    wcel
    #
    @11
    cxr
    wcel
    @91
    @82
    @92
    @80
    @10
    cr
    vx
    vuniex
    elpw
    biimpri
    @92
    @2
    cxr
    @11
    cc0
    cpnf
    iccssxr
    @0
    @2
    @10
    cdde
    @27
    ffvelrni
    sseldi
    @11
    xaddid1
    4syl
    adantr
    3eqtrrd
    adantrl
    ex
    rgen
    @0
    cr
    csiga
    cfv
    wcel
    #
    @0
    csiga
    crn
    cuni
    wcel
    @1
    @3
    @4
    @17
    w3a
    wb
    cr
    cvv
    wcel
    @93
    reex
    cr
    cvv
    pwsiga
    ax-mp
    @0
    cr
    elrnsiga
    vx
    vy
    @0
    cdde
    ismeas
    mp2b
    mpbir3an
end
