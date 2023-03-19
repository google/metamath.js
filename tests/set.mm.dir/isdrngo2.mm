include "cdrng.mm"
include "wcel.mm"
include "crngo.mm"
include "csn.mm"
include "cdif.mm"
include "cxp.mm"
include "cres.mm"
include "cgr.mm"
include "wa.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "isdrngo1.mm"
include "dvrunz.mm"
include "sylbir.mm"
include "crn.mm"
include "cdm.mm"
include "grporndm.mm"
include "adantl.mm"
include "wss.mm"
include "difss.mm"
include "xpss12.mm"
include "mp2an.mm"
include "wf.mm"
include "rngosm.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseqr.mm"
include "adantr.mm"
include "ssdmres.mm"
include "sylib.mm"
include "dmeqd.mm"
include "dmxpid.mm"
include "syl6eq.mm"
include "eqtrd.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "cgn.mm"
include "cfv.mm"
include "eqid.mm"
include "grpoinvcl.mm"
include "adantll.mm"
include "cgi.mm"
include "grpolinv.mm"
include "cmagm.mm"
include "cexid.mm"
include "cin.mm"
include "cmndo.mm"
include "rngomndo.mm"
include "mndomgmid.mm"
include "sseqtri.mm"
include "rngorn1eq.mm"
include "syl5sseq.mm"
include "c1st.mm"
include "rneqi.mm"
include "eqtri.mm"
include "rngo1cl.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "grpomndo.mm"
include "mndoismgmOLD.mm"
include "exidresid.mm"
include "syl31anc.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "syldan.mm"
include "rexeqdv.mm"
include "wb.mm"
include "ovres.mm"
include "ancoms.mm"
include "rexbidva.mm"
include "bitrd.mm"
include "mpbid.mm"
include "ralrimiva.mm"
include "jca.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rnex.mm"
include "difexg.mm"
include "mp1i.mm"
include "wfn.mm"
include "ffn.mm"
include "fnssres.mm"
include "sylancl.mm"
include "eldifi.mm"
include "anim12i.mm"
include "rngocl.mm"
include "3expb.mm"
include "sylan2.mm"
include "adantlr.mm"
include "weq.mm"
include "oveq2.mm"
include "rexbidv.mm"
include "rspcv.mm"
include "imdistanri.mm"
include "wi.mm"
include "ssrexv.mm"
include "ax-mp.mm"
include "zerdivemp1x.mm"
include "syl3an3.mm"
include "syl3an2.mm"
include "imp.mm"
include "necon3d.mm"
include "impr.mm"
include "sylan2b.mm"
include "an32s.mm"
include "ancom2s.mm"
include "an42s.mm"
include "adantlrl.mm"
include "eqeltrd.mm"
include "ralrimivva.mm"
include "ffnov.mm"
include "w3a.mm"
include "3adantr3.mm"
include "simpr3.mm"
include "ovresd.mm"
include "3adant3.mm"
include "oveq1d.mm"
include "3adant1.mm"
include "oveq2d.mm"
include "simpr1.mm"
include "fovrn.mm"
include "3adant3r1.mm"
include "sylan.mm"
include "3anim123i.mm"
include "rngoass.mm"
include "3eqtr4d.mm"
include "anim1i.mm"
include "sylibr.mm"
include "adantrr.mm"
include "rngolidm.mm"
include "adantlrr.mm"
include "rspcva.mm"
include "cbvrexv.mm"
include "isgrpda.mm"
include "impbida.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem isdrngo2
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cU: class U
  let cG: class G
  let cH: class H
  let cX: class X
  let cZ: class Z
  let vg: setvar g
  let vh: setvar h
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  assume isdivrng1.1: |- G = ( 1st ` R )
  assume isdivrng1.2: |- H = ( 2nd ` R )
  assume isdivrng1.3: |- Z = ( GId ` G )
  assume isdivrng1.4: |- X = ran G
  assume isdivrng2.5: |- U = ( GId ` H )

  disjoint H x
  disjoint H y
  disjoint x y
  disjoint X x
  disjoint X y
  disjoint Z x
  disjoint Z y
  disjoint R x
  disjoint R y
  disjoint U x
  disjoint U y
  disjoint g h
  disjoint H u
  disjoint H v
  disjoint H w
  disjoint H z
  disjoint u x
  disjoint v x
  disjoint w x
  disjoint x z
  disjoint u y
  disjoint v y
  disjoint w y
  disjoint y z
  disjoint u v
  disjoint u w
  disjoint u z
  disjoint v w
  disjoint v z
  disjoint w z
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X z
  disjoint Z u
  disjoint Z v
  disjoint Z w
  disjoint Z z
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint R z
  disjoint U u
  disjoint U v
  disjoint U w
  disjoint U z
  assert |- ( R e. DivRingOps <-> ( R e. RingOps /\ ( U =/= Z /\ A. x e. ( X \ { Z } ) E. y e. ( X \ { Z } ) ( y H x ) = U ) ) )

  proof
    cR
    cdrng
    wcel
    #
    cR
    crngo
    wcel
    #
    cH
    cX
    cZ
    csn
    #
    cdif
    #
    @3
    cxp
    #
    cres
    #
    cgr
    wcel
    #
    wa
    #
    @1
    cU
    cZ
    wne
    #
    vy
    cv
    #
    vx
    cv
    #
    cH
    co
    #
    cU
    wceq
    #
    vy
    @3
    wrex
    #
    vx
    @3
    wral
    #
    wa
    #
    wa
    #
    cR
    cG
    cH
    cX
    cZ
    isdivrng1.1
    isdivrng1.2
    isdivrng1.3
    isdivrng1.4
    isdrngo1
    #
    @1
    @6
    @15
    @1
    @6
    @15
    @7
    @8
    @14
    @7
    @0
    @8
    @17
    cR
    cU
    cG
    cH
    cX
    cZ
    isdivrng1.1
    isdivrng1.2
    isdivrng1.4
    isdivrng1.3
    isdivrng2.5
    dvrunz
    sylbir
    #
    @7
    @13
    vx
    @3
    @7
    @10
    @3
    wcel
    #
    wa
    #
    @9
    @10
    @5
    co
    #
    cU
    wceq
    #
    vy
    @5
    crn
    #
    wrex
    #
    @13
    @7
    @19
    @10
    @23
    wcel
    #
    @24
    @7
    @25
    @19
    @7
    @23
    @3
    @10
    @7
    @23
    @5
    cdm
    #
    cdm
    #
    @3
    @6
    @23
    @27
    wceq
    @1
    @5
    grporndm
    adantl
    @7
    @27
    @4
    cdm
    @3
    @7
    @26
    @4
    @7
    @4
    cH
    cdm
    #
    wss
    #
    @26
    @4
    wceq
    @1
    @29
    @6
    @1
    cX
    cX
    cxp
    #
    @4
    @28
    @3
    cX
    wss
    #
    @31
    @4
    @30
    wss
    #
    cX
    @2
    difss
    #
    @33
    @3
    cX
    @3
    cX
    xpss12
    mp2an
    #
    @1
    @30
    cX
    cH
    wf
    #
    @28
    @30
    wceq
    cR
    cG
    cH
    cX
    isdivrng1.1
    isdivrng1.2
    isdivrng1.4
    rngosm
    #
    @30
    cX
    cH
    fdm
    syl
    syl5sseqr
    adantr
    @4
    cH
    ssdmres
    sylib
    dmeqd
    @3
    dmxpid
    syl6eq
    eqtrd
    #
    eleq2d
    biimpar
    @7
    @25
    wa
    #
    @10
    @5
    cgn
    cfv
    #
    cfv
    #
    @23
    wcel
    #
    @40
    @10
    @5
    co
    #
    cU
    wceq
    #
    @24
    @6
    @25
    @41
    @1
    @10
    @5
    @39
    @23
    @23
    eqid
    #
    @39
    eqid
    #
    grpoinvcl
    adantll
    @38
    @42
    @5
    cgi
    cfv
    #
    cU
    @6
    @25
    @42
    @46
    wceq
    @1
    @10
    @46
    @5
    @39
    @23
    @44
    @46
    eqid
    @45
    grpolinv
    adantll
    @7
    @46
    cU
    wceq
    #
    @25
    @7
    cH
    cmagm
    cexid
    cin
    wcel
    #
    @3
    cH
    crn
    #
    wss
    #
    cU
    @3
    wcel
    #
    @5
    cmagm
    wcel
    #
    @47
    @1
    @48
    @6
    @1
    cH
    cmndo
    wcel
    @48
    cR
    cH
    isdivrng1.2
    rngomndo
    cH
    mndomgmid
    syl
    adantr
    @1
    @50
    @6
    @1
    cG
    crn
    #
    @3
    @49
    @3
    cX
    @53
    @33
    isdivrng1.4
    sseqtri
    cR
    cG
    cH
    isdivrng1.2
    isdivrng1.1
    rngorn1eq
    syl5sseq
    adantr
    @7
    cU
    cX
    wcel
    #
    @8
    @51
    @1
    @54
    @6
    cR
    cU
    cH
    cX
    cX
    @53
    cR
    c1st
    cfv
    #
    crn
    isdivrng1.4
    cG
    @55
    isdivrng1.1
    rneqi
    eqtri
    #
    isdivrng1.2
    isdivrng2.5
    rngo1cl
    #
    adantr
    @18
    cU
    cX
    cZ
    eldifsn
    #
    sylanbrc
    @6
    @52
    @1
    @6
    @5
    cmndo
    wcel
    @52
    @5
    grpomndo
    @5
    mndoismgmOLD
    syl
    adantl
    cU
    cH
    @5
    @49
    @3
    @49
    eqid
    isdivrng2.5
    @5
    eqid
    exidresid
    syl31anc
    adantr
    eqtrd
    @22
    @43
    vy
    @40
    @23
    @9
    @40
    wceq
    @21
    @42
    cU
    @9
    @40
    @10
    @5
    oveq1
    eqeq1d
    rspcev
    syl2anc
    syldan
    @20
    @24
    @22
    vy
    @3
    wrex
    #
    @13
    @20
    @22
    vy
    @23
    @3
    @7
    @23
    @3
    wceq
    @19
    @37
    adantr
    rexeqdv
    @19
    @59
    @13
    wb
    @7
    @19
    @22
    @12
    vy
    @3
    @19
    @9
    @3
    wcel
    #
    wa
    @21
    @11
    cU
    @60
    @19
    @21
    @11
    wceq
    @9
    @10
    @3
    @3
    cH
    ovres
    ancoms
    eqeq1d
    rexbidva
    adantl
    bitrd
    mpbid
    ralrimiva
    jca
    @16
    vu
    vv
    vw
    cU
    vz
    @5
    @3
    cX
    cvv
    wcel
    @3
    cvv
    wcel
    @16
    cX
    @53
    cvv
    isdivrng1.4
    cG
    cG
    @55
    cvv
    isdivrng1.1
    cR
    c1st
    fvex
    eqeltri
    rnex
    eqeltri
    cX
    @2
    cvv
    difexg
    mp1i
    @16
    @5
    @4
    wfn
    #
    vu
    cv
    #
    vv
    cv
    #
    @5
    co
    #
    @3
    wcel
    #
    vv
    @3
    wral
    vu
    @3
    wral
    @4
    @3
    @5
    wf
    #
    @16
    cH
    @30
    wfn
    #
    @32
    @61
    @1
    @67
    @15
    @1
    @35
    @67
    @36
    @30
    cX
    cH
    ffn
    syl
    adantr
    @34
    @30
    @4
    cH
    fnssres
    sylancl
    @16
    @65
    vu
    vv
    @3
    @3
    @16
    @62
    @3
    wcel
    #
    @63
    @3
    wcel
    #
    wa
    #
    wa
    #
    @64
    @62
    @63
    cH
    co
    #
    @3
    @70
    @64
    @72
    wceq
    #
    @16
    @62
    @63
    @3
    @3
    cH
    ovres
    #
    adantl
    @71
    @72
    cX
    wcel
    #
    @72
    cZ
    wne
    #
    @72
    @3
    wcel
    #
    @1
    @70
    @75
    @15
    @70
    @1
    @62
    cX
    wcel
    #
    @63
    cX
    wcel
    #
    wa
    @75
    @68
    @78
    @69
    @79
    @62
    cX
    @2
    eldifi
    #
    @63
    cX
    @2
    eldifi
    #
    anim12i
    @1
    @78
    @79
    @75
    @62
    @63
    cR
    cG
    cH
    cX
    isdivrng1.1
    isdivrng1.2
    isdivrng1.4
    rngocl
    3expb
    sylan2
    adantlr
    @1
    @14
    @70
    @76
    @8
    @1
    @69
    @14
    @68
    @76
    @14
    @68
    wa
    @1
    @69
    wa
    #
    @9
    @62
    cH
    co
    #
    cU
    wceq
    #
    vy
    @3
    wrex
    #
    @68
    wa
    @76
    @68
    @14
    @85
    @13
    @85
    vx
    @62
    @3
    vx
    vu
    weq
    #
    @12
    @84
    vy
    @3
    @86
    @11
    @83
    cU
    @10
    @62
    @9
    cH
    oveq2
    eqeq1d
    rexbidv
    #
    rspcv
    imdistanri
    @82
    @68
    @85
    @76
    @1
    @68
    @85
    wa
    #
    @69
    @76
    @69
    @1
    @88
    wa
    #
    @79
    @63
    cZ
    wne
    #
    wa
    @76
    @63
    cX
    cZ
    eldifsn
    @89
    @79
    @90
    @76
    @89
    @79
    wa
    @72
    cZ
    @63
    cZ
    @89
    @79
    @72
    cZ
    wceq
    @63
    cZ
    wceq
    wi
    #
    @1
    @68
    @85
    @79
    @91
    wi
    #
    @68
    @1
    @78
    @85
    @92
    @80
    @85
    @1
    @78
    @84
    vy
    cX
    wrex
    #
    @92
    @31
    @85
    @93
    wi
    @33
    @84
    vy
    @3
    cX
    ssrexv
    ax-mp
    @62
    @63
    cR
    cU
    cG
    cH
    cX
    cZ
    vy
    isdivrng1.1
    isdivrng1.2
    isdivrng1.3
    isdivrng1.4
    isdivrng2.5
    zerdivemp1x
    syl3an3
    syl3an2
    3expb
    imp
    necon3d
    impr
    sylan2b
    an32s
    ancom2s
    sylan2
    an42s
    adantlrl
    @72
    cX
    cZ
    eldifsn
    sylanbrc
    #
    eqeltrd
    ralrimivva
    vu
    vv
    @3
    @3
    @3
    @5
    ffnov
    sylanbrc
    #
    @16
    @68
    @69
    vw
    cv
    #
    @3
    wcel
    #
    w3a
    #
    wa
    #
    @72
    @96
    @5
    co
    @72
    @96
    cH
    co
    #
    @64
    @96
    @5
    co
    @62
    @63
    @96
    @5
    co
    #
    @5
    co
    #
    @99
    @72
    @96
    cH
    @3
    @16
    @68
    @69
    @77
    @97
    @94
    3adantr3
    @16
    @68
    @69
    @97
    simpr3
    ovresd
    @99
    @64
    @72
    @96
    @5
    @98
    @73
    @16
    @68
    @69
    @73
    @97
    @74
    3adant3
    adantl
    oveq1d
    @99
    @62
    @101
    cH
    co
    @62
    @63
    @96
    cH
    co
    #
    cH
    co
    #
    @102
    @100
    @99
    @101
    @103
    @62
    cH
    @98
    @101
    @103
    wceq
    #
    @16
    @69
    @97
    @105
    @68
    @63
    @96
    @3
    @3
    cH
    ovres
    3adant1
    adantl
    oveq2d
    @99
    @62
    @101
    cH
    @3
    @16
    @68
    @69
    @97
    simpr1
    @16
    @66
    @98
    @101
    @3
    wcel
    #
    @95
    @66
    @69
    @97
    @106
    @68
    @63
    @96
    @3
    @3
    @3
    @5
    fovrn
    3adant3r1
    sylan
    ovresd
    @1
    @98
    @100
    @104
    wceq
    #
    @15
    @98
    @1
    @78
    @79
    @96
    cX
    wcel
    #
    w3a
    @107
    @68
    @78
    @69
    @79
    @97
    @108
    @80
    @81
    @96
    cX
    @2
    eldifi
    3anim123i
    @62
    @63
    @96
    cR
    cG
    cH
    cX
    isdivrng1.1
    isdivrng1.2
    isdivrng1.4
    rngoass
    sylan2
    adantlr
    3eqtr4d
    3eqtr4d
    @1
    @8
    @51
    @14
    @1
    @8
    wa
    #
    @54
    @8
    wa
    @51
    @1
    @54
    @8
    @57
    anim1i
    @58
    sylibr
    #
    adantrr
    @1
    @8
    @68
    cU
    @62
    @5
    co
    #
    @62
    wceq
    @14
    @109
    @68
    wa
    @111
    cU
    @62
    cH
    co
    #
    @62
    @109
    @51
    @68
    @111
    @112
    wceq
    @110
    cU
    @62
    @3
    @3
    cH
    ovres
    sylan
    @1
    @68
    @112
    @62
    wceq
    #
    @8
    @68
    @1
    @78
    @113
    @80
    @62
    cR
    cU
    cH
    cX
    isdivrng1.2
    @56
    isdivrng2.5
    rngolidm
    sylan2
    adantlr
    eqtrd
    adantlrr
    @1
    @14
    @68
    vz
    cv
    #
    @62
    @5
    co
    #
    cU
    wceq
    #
    vz
    @3
    wrex
    #
    @8
    @14
    @68
    @117
    @1
    @68
    @14
    @117
    @68
    @14
    @85
    @117
    @13
    @85
    vx
    @62
    @3
    @87
    rspcva
    @85
    @68
    @114
    @62
    cH
    co
    #
    cU
    wceq
    #
    vz
    @3
    wrex
    #
    @117
    @84
    @119
    vy
    vz
    @3
    vy
    vz
    weq
    @83
    @118
    cU
    @9
    @114
    @62
    cH
    oveq1
    eqeq1d
    cbvrexv
    @68
    @117
    @120
    @68
    @116
    @119
    vz
    @3
    @114
    @3
    wcel
    #
    @68
    @116
    @119
    wb
    @121
    @68
    wa
    @115
    @118
    cU
    @114
    @62
    @3
    @3
    cH
    ovres
    eqeq1d
    ancoms
    rexbidva
    biimpar
    sylan2b
    syldan
    ancoms
    adantll
    adantlrl
    isgrpda
    impbida
    pm5.32i
    bitri
end
