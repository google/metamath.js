include "cmap.mm"
include "co.mm"
include "ciun.mm"
include "cv.mm"
include "wf.mm"
include "csb.mm"
include "cfv.mm"
include "wf1.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "cxp.mm"
include "cdom.mm"
include "wbr.mm"
include "wacn.mm"
include "wcel.mm"
include "wrex.mm"
include "brdomi.mm"
include "adantl.mm"
include "f1f.mm"
include "wb.mm"
include "cvv.mm"
include "reldom.mm"
include "brrelex2i.mm"
include "brrelexi.mm"
include "elmapd.mm"
include "syl5ibr.mm"
include "wss.mm"
include "ssiun2.mm"
include "adantr.mm"
include "sseld.mm"
include "syld.mm"
include "ancrd.mm"
include "eximdv.mm"
include "mpd.mm"
include "df-rex.mm"
include "sylibr.mm"
include "ralimiaa.mm"
include "syl.mm"
include "nfv.mm"
include "nfiu1.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nff1.mm"
include "nfrex.mm"
include "weq.mm"
include "wceq.mm"
include "csbeq1a.mm"
include "f1eq2.mm"
include "rexbidv.mm"
include "cbvral.mm"
include "sylib.mm"
include "f1eq1.mm"
include "acni3.mm"
include "syl2anc.mm"
include "fveq2.mm"
include "bitrd.mm"
include "c0.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "acnrcl.mm"
include "wi.mm"
include "r19.2z.mm"
include "rexlimivw.mm"
include "expcom.mm"
include "xpexg.mm"
include "syl6an.mm"
include "syl5bir.mm"
include "xpeq1.mm"
include "0xp.mm"
include "0ex.mm"
include "eqeltri.mm"
include "syl6eqel.mm"
include "pm2.61d2.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "csn.mm"
include "eleq2i.mm"
include "eliun.mm"
include "bitri.mm"
include "r19.29.mm"
include "xp1st.mm"
include "ad2antll.mm"
include "elsni.mm"
include "simpl.mm"
include "eqeltrd.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "ad2antrl.mm"
include "xp2nd.mm"
include "ffvelrnd.mm"
include "opelxpi.mm"
include "rexlimiva.mm"
include "ex.mm"
include "syl5bi.mm"
include "fvex.mm"
include "opth.mm"
include "simpr.mm"
include "eqeq2d.mm"
include "djussxp.mm"
include "eqsstri.mm"
include "simprl.mm"
include "sseldi.mm"
include "simpll.mm"
include "rspc.mm"
include "sylc.mm"
include "nfel2.mm"
include "eqcomd.mm"
include "eleqtrd.mm"
include "rexlimi.mm"
include "imp.mm"
include "adantrr.mm"
include "ralrimiv.mm"
include "csbeq1d.mm"
include "eleq12d.mm"
include "rspccva.mm"
include "sylan.mm"
include "adantrl.mm"
include "eleqtrrd.mm"
include "f1fveq.mm"
include "syl12anc.mm"
include "bitr3d.mm"
include "pm5.32da.mm"
include "simprr.mm"
include "xpopth.mm"
include "syl5bb.mm"
include "dom2d.mm"
include "syl5com.mm"
include "adantld.mm"
include "exlimdv.mm"

theorem iundom2g
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y
  let vz: setvar z
  assume iunfo.1: |- T = U_ x e. A ( { x } X. B )
  assume iundomg.2: |- ( ph -> U_ x e. A ( C ^m B ) e. AC_ A )
  assume iundomg.3: |- ( ph -> A. x e. A B ~<_ C )

  disjoint A x
  disjoint C x
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B f
  disjoint B g
  disjoint B y
  disjoint B z
  disjoint C f
  disjoint C g
  disjoint C y
  disjoint C z
  disjoint T f
  disjoint T y
  disjoint T z
  disjoint f ph
  assert |- ( ph -> T ~<_ ( A X. C ) )

  proof
    wph
    cA
    vx
    cA
    cC
    cB
    cmap
    co
    #
    ciun
    #
    vf
    cv
    #
    wf
    #
    vx
    vy
    cv
    #
    cB
    csb
    #
    cC
    @4
    @2
    cfv
    #
    wf1
    #
    vy
    cA
    wral
    #
    wa
    #
    vf
    wex
    #
    cT
    cA
    cC
    cxp
    #
    cdom
    wbr
    #
    wph
    @1
    cA
    wacn
    wcel
    #
    @5
    cC
    vg
    cv
    #
    wf1
    #
    vg
    @1
    wrex
    #
    vy
    cA
    wral
    #
    @10
    iundomg.2
    wph
    cB
    cC
    @14
    wf1
    #
    vg
    @1
    wrex
    #
    vx
    cA
    wral
    #
    @17
    wph
    cB
    cC
    cdom
    wbr
    #
    vx
    cA
    wral
    #
    @20
    iundomg.3
    @21
    @19
    vx
    cA
    vx
    cv
    #
    cA
    wcel
    #
    @21
    wa
    #
    @14
    @1
    wcel
    #
    @18
    wa
    #
    vg
    wex
    #
    @19
    @25
    @18
    vg
    wex
    #
    @28
    @21
    @29
    @24
    cB
    cC
    vg
    brdomi
    adantl
    @25
    @18
    @27
    vg
    @25
    @18
    @26
    @25
    @18
    @14
    @0
    wcel
    #
    @26
    @18
    @30
    @25
    cB
    cC
    @14
    wf
    #
    cB
    cC
    @14
    f1f
    @21
    @30
    @31
    wb
    @24
    @21
    cC
    cB
    @14
    cvv
    cvv
    cB
    cC
    cdom
    reldom
    brrelex2i
    #
    cB
    cC
    cdom
    reldom
    brrelexi
    elmapd
    adantl
    syl5ibr
    @25
    @0
    @1
    @14
    @24
    @0
    @1
    wss
    @21
    vx
    cA
    @0
    ssiun2
    adantr
    sseld
    syld
    ancrd
    eximdv
    mpd
    @18
    vg
    @1
    df-rex
    sylibr
    ralimiaa
    syl
    @19
    @16
    vx
    vy
    cA
    @19
    vy
    nfv
    @15
    vx
    vg
    @1
    vx
    cA
    @0
    nfiu1
    vx
    @5
    cC
    @14
    vx
    @14
    nfcv
    vx
    @4
    cB
    nfcsb1v
    #
    vx
    cC
    nfcv
    #
    nff1
    nfrex
    vx
    vy
    weq
    #
    @18
    @15
    vg
    @1
    @35
    cB
    @5
    wceq
    #
    @18
    @15
    wb
    vx
    @4
    cB
    csbeq1a
    #
    cB
    @5
    cC
    @14
    f1eq2
    syl
    rexbidv
    cbvral
    sylib
    @15
    @7
    vy
    vg
    cA
    vf
    @1
    @5
    cC
    @14
    @6
    f1eq1
    acni3
    syl2anc
    wph
    @9
    @12
    vf
    wph
    @8
    @12
    @3
    @8
    cB
    cC
    @23
    @2
    cfv
    #
    wf1
    #
    vx
    cA
    wral
    #
    wph
    @12
    @39
    @7
    vx
    vy
    cA
    @39
    vy
    nfv
    vx
    @5
    cC
    @6
    vx
    @6
    nfcv
    @33
    @34
    nff1
    @35
    @39
    cB
    cC
    @6
    wf1
    #
    @7
    @35
    @38
    @6
    wceq
    @39
    @41
    wb
    @23
    @4
    @2
    fveq2
    cB
    cC
    @38
    @6
    f1eq1
    syl
    @35
    @36
    @41
    @7
    wb
    @37
    cB
    @5
    cC
    @6
    f1eq2
    syl
    bitrd
    cbvral
    wph
    @11
    cvv
    wcel
    #
    @40
    @12
    wph
    cA
    c0
    wceq
    #
    @42
    @43
    wn
    cA
    c0
    wne
    #
    wph
    @42
    cA
    c0
    df-ne
    wph
    cA
    cvv
    wcel
    #
    @44
    cC
    cvv
    wcel
    #
    @42
    wph
    @13
    @45
    iundomg.2
    cA
    @1
    acnrcl
    syl
    wph
    @22
    @44
    @46
    wi
    iundomg.3
    @44
    @22
    @46
    @44
    @22
    wa
    @21
    vx
    cA
    wrex
    @46
    @21
    vx
    cA
    r19.2z
    @21
    @46
    vx
    cA
    @32
    rexlimivw
    syl
    expcom
    syl
    cA
    cC
    cvv
    cvv
    xpexg
    syl6an
    syl5bir
    @43
    @11
    c0
    cC
    cxp
    #
    cvv
    cA
    c0
    cC
    xpeq1
    @47
    c0
    cvv
    cC
    0xp
    0ex
    eqeltri
    syl6eqel
    pm2.61d2
    @40
    vy
    vz
    cT
    @11
    @4
    c1st
    cfv
    #
    @4
    c2nd
    cfv
    #
    @48
    @2
    cfv
    #
    cfv
    #
    cop
    #
    vz
    cv
    #
    c1st
    cfv
    #
    @53
    c2nd
    cfv
    #
    @54
    @2
    cfv
    #
    cfv
    #
    cop
    #
    cvv
    @4
    cT
    wcel
    #
    @4
    @23
    csn
    #
    cB
    cxp
    #
    wcel
    #
    vx
    cA
    wrex
    #
    @40
    @52
    @11
    wcel
    #
    @59
    @4
    vx
    cA
    @61
    ciun
    #
    wcel
    @63
    cT
    @65
    @4
    iunfo.1
    eleq2i
    vx
    @4
    cA
    @61
    eliun
    bitri
    #
    @40
    @63
    @64
    @40
    @63
    wa
    #
    @39
    @62
    wa
    #
    vx
    cA
    wrex
    #
    @64
    @39
    @62
    vx
    cA
    r19.29
    #
    @68
    @64
    vx
    cA
    @24
    @68
    wa
    #
    @48
    cA
    wcel
    #
    @51
    cC
    wcel
    @64
    @71
    @48
    @23
    cA
    @71
    @48
    @60
    wcel
    #
    @48
    @23
    wceq
    @62
    @73
    @24
    @39
    @4
    @60
    cB
    xp1st
    ad2antll
    @48
    @23
    elsni
    syl
    #
    @24
    @68
    simpl
    eqeltrd
    @71
    @51
    @49
    @38
    cfv
    cC
    @71
    @49
    @50
    @38
    @71
    @48
    @23
    @2
    @74
    fveq2d
    fveq1d
    @71
    cB
    cC
    @49
    @38
    @39
    cB
    cC
    @38
    wf
    @24
    @62
    cB
    cC
    @38
    f1f
    ad2antrl
    @62
    @49
    cB
    wcel
    @24
    @39
    @4
    @60
    cB
    xp2nd
    ad2antll
    #
    ffvelrnd
    eqeltrd
    @48
    @51
    cA
    cC
    opelxpi
    syl2anc
    rexlimiva
    syl
    ex
    syl5bi
    @40
    @59
    @53
    cT
    wcel
    #
    wa
    #
    @52
    @58
    wceq
    #
    vy
    vz
    weq
    #
    wb
    @78
    @48
    @54
    wceq
    #
    @51
    @57
    wceq
    #
    wa
    #
    @40
    @77
    wa
    #
    @79
    @48
    @51
    @54
    @57
    @4
    c1st
    fvex
    @49
    @50
    fvex
    opth
    @83
    @82
    @80
    @49
    @55
    wceq
    #
    wa
    #
    @79
    @83
    @80
    @81
    @84
    @83
    @80
    wa
    #
    @51
    @55
    @50
    cfv
    #
    wceq
    #
    @81
    @84
    @86
    @87
    @57
    @51
    @86
    @55
    @50
    @56
    @86
    @48
    @54
    @2
    @83
    @80
    simpr
    #
    fveq2d
    fveq1d
    eqeq2d
    @86
    vx
    @48
    cB
    csb
    #
    cC
    @50
    wf1
    #
    @49
    @90
    wcel
    #
    @55
    @90
    wcel
    @88
    @84
    wb
    @86
    @72
    @40
    @91
    @86
    @4
    cA
    cvv
    cxp
    #
    wcel
    #
    @72
    @83
    @94
    @80
    @83
    cT
    @93
    @4
    cT
    @65
    @93
    iunfo.1
    vx
    cA
    cB
    djussxp
    eqsstri
    #
    @40
    @59
    @76
    simprl
    sseldi
    #
    adantr
    @4
    cA
    cvv
    xp1st
    syl
    @40
    @77
    @80
    simpll
    @39
    @91
    vx
    @48
    cA
    vx
    @90
    cC
    @50
    vx
    @50
    nfcv
    vx
    @48
    cB
    nfcsb1v
    #
    @34
    nff1
    @23
    @48
    wceq
    #
    @39
    cB
    cC
    @50
    wf1
    #
    @91
    @98
    @38
    @50
    wceq
    @39
    @99
    wb
    @23
    @48
    @2
    fveq2
    cB
    cC
    @38
    @50
    f1eq1
    syl
    @98
    cB
    @90
    wceq
    #
    @99
    @91
    wb
    vx
    @48
    cB
    csbeq1a
    #
    cB
    @90
    cC
    @50
    f1eq2
    syl
    bitrd
    rspc
    sylc
    @83
    @92
    @80
    @40
    @59
    @92
    @76
    @40
    @59
    @92
    @59
    @63
    @40
    @92
    @66
    @40
    @63
    @92
    @67
    @69
    @92
    @70
    @68
    @92
    vx
    cA
    vx
    @49
    @90
    @97
    nfel2
    @24
    @68
    @92
    @71
    @49
    cB
    @90
    @75
    @71
    @98
    @100
    @71
    @48
    @23
    @74
    eqcomd
    @101
    syl
    eleqtrd
    ex
    rexlimi
    syl
    ex
    syl5bi
    #
    imp
    adantrr
    adantr
    @86
    @55
    vx
    @54
    cB
    csb
    #
    @90
    @83
    @55
    @103
    wcel
    #
    @80
    @40
    @76
    @104
    @59
    @40
    @92
    vy
    cT
    wral
    @76
    @104
    @40
    @92
    vy
    cT
    @102
    ralrimiv
    @92
    @104
    vy
    @53
    cT
    @79
    @49
    @55
    @90
    @103
    @4
    @53
    c2nd
    fveq2
    @79
    vx
    @48
    @54
    cB
    @4
    @53
    c1st
    fveq2
    csbeq1d
    eleq12d
    rspccva
    sylan
    adantrl
    adantr
    @86
    vx
    @48
    @54
    cB
    @89
    csbeq1d
    eleqtrrd
    @90
    cC
    @49
    @55
    @50
    f1fveq
    syl12anc
    bitr3d
    pm5.32da
    @83
    @94
    @53
    @93
    wcel
    @85
    @79
    wb
    @96
    @83
    cT
    @93
    @53
    @95
    @40
    @59
    @76
    simprr
    sseldi
    @4
    @53
    cA
    cvv
    cA
    cvv
    xpopth
    syl2anc
    bitrd
    syl5bb
    ex
    dom2d
    syl5com
    syl5bir
    adantld
    exlimdv
    mpd
end
