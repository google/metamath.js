include "cv.mm"
include "cslt.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "csur.mm"
include "wss.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "csuc.mm"
include "cres.mm"
include "wceq.mm"
include "wi.mm"
include "w3a.mm"
include "cfv.mm"
include "cin.mm"
include "dmres.mm"
include "word.mm"
include "nosupno.mm"
include "3ad2ant2.mm"
include "nodmord.mm"
include "syl.mm"
include "cab.mm"
include "dmeq.mm"
include "eleq2d.mm"
include "breq2.mm"
include "notbid.mm"
include "reseq1.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "3impb.mm"
include "weq.mm"
include "cbvrexv.mm"
include "sylibr.mm"
include "wb.mm"
include "eleq1.mm"
include "suceq.mm"
include "reseq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "rexbidv.mm"
include "elabg.mm"
include "mpbird.mm"
include "3ad2ant3.mm"
include "cio.mm"
include "cmpt.mm"
include "crio.mm"
include "c2o.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "cif.mm"
include "iffalse.mm"
include "syl5eq.mm"
include "dmeqd.mm"
include "iotaex.mm"
include "eqid.mm"
include "dmmpti.mm"
include "syl6eq.mm"
include "3ad2ant1.mm"
include "eleqtrrd.mm"
include "ordsucss.mm"
include "sylc.mm"
include "df-ss.mm"
include "sylib.mm"
include "simp2l.mm"
include "simp31.mm"
include "sseldd.mm"
include "simp32.mm"
include "eqtr4d.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl31.mm"
include "sselda.mm"
include "con0.mm"
include "nodmon.mm"
include "onelon.mm"
include "syl2anc.mm"
include "eloni.mm"
include "ordsuc.mm"
include "imp.mm"
include "simpl33.mm"
include "resabs1.mm"
include "syl5ib.mm"
include "imim2d.mm"
include "ralimdv.mm"
include "nosupfv.mm"
include "syl113anc.mm"
include "simpr.mm"
include "fvresd.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "wfun.mm"
include "nofun.mm"
include "funres.mm"
include "3syl.mm"
include "eqfunfv.mm"
include "mpbir2and.mm"

theorem nosupres
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cS: class S
  let cU: class U
  let vg: setvar g
  let cG: class G
  let va: setvar a
  let vp: setvar p
  assume nosupres.1: |- S = if ( E. x e. A A. y e. A -. x <s y , ( ( iota_ x e. A A. y e. A -. x <s y ) u. { <. dom ( iota_ x e. A A. y e. A -. x <s y ) , 2o >. } ) , ( g e. { y | E. u e. A ( y e. dom u /\ A. v e. A ( -. v <s u -> ( u |` suc y ) = ( v |` suc y ) ) ) } |-> ( iota x E. u e. A ( g e. dom u /\ A. v e. A ( -. v <s u -> ( u |` suc g ) = ( v |` suc g ) ) /\ ( u ` g ) = x ) ) ) )

  disjoint A g
  disjoint A u
  disjoint A v
  disjoint A x
  disjoint A y
  disjoint g u
  disjoint G u
  disjoint g v
  disjoint G v
  disjoint g x
  disjoint g y
  disjoint G y
  disjoint U u
  disjoint u v
  disjoint U v
  disjoint u x
  disjoint U x
  disjoint u y
  disjoint v x
  disjoint v y
  disjoint x y
  disjoint A a
  disjoint a g
  disjoint A p
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint G a
  disjoint G p
  disjoint p u
  disjoint p v
  disjoint S a
  disjoint U a
  disjoint U p
  assert |- ( ( -. E. x e. A A. y e. A -. x <s y /\ ( A C_ No /\ A e. _V ) /\ ( U e. A /\ G e. dom U /\ A. v e. A ( -. v <s U -> ( U |` suc G ) = ( v |` suc G ) ) ) ) -> ( S |` suc G ) = ( U |` suc G ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cslt
    wbr
    wn
    vy
    cA
    wral
    #
    vx
    cA
    wrex
    #
    wn
    #
    cA
    csur
    wss
    #
    cA
    cvv
    wcel
    #
    wa
    #
    cU
    cA
    wcel
    #
    cG
    cU
    cdm
    #
    wcel
    #
    vv
    cv
    #
    cU
    cslt
    wbr
    #
    wn
    #
    cU
    cG
    csuc
    #
    cres
    #
    @11
    @14
    cres
    #
    wceq
    #
    wi
    #
    vv
    cA
    wral
    #
    w3a
    #
    w3a
    #
    cS
    @14
    cres
    #
    @15
    wceq
    #
    @22
    cdm
    #
    @15
    cdm
    #
    wceq
    #
    va
    cv
    #
    @22
    cfv
    #
    @27
    @15
    cfv
    #
    wceq
    #
    va
    @24
    wral
    #
    @21
    @24
    @14
    @25
    @21
    @24
    @14
    cS
    cdm
    #
    cin
    #
    @14
    cS
    @14
    dmres
    @21
    @14
    @32
    wss
    #
    @33
    @14
    wceq
    @21
    @32
    word
    #
    cG
    @32
    wcel
    @34
    @21
    cS
    csur
    wcel
    #
    @35
    @7
    @4
    @36
    @20
    vx
    vy
    vv
    vu
    cA
    cS
    vg
    cvv
    nosupres.1
    nosupno
    3ad2ant2
    #
    cS
    nodmord
    syl
    @21
    cG
    @1
    vu
    cv
    #
    cdm
    #
    wcel
    #
    @11
    @38
    cslt
    wbr
    #
    wn
    #
    @38
    @1
    csuc
    #
    cres
    #
    @11
    @43
    cres
    #
    wceq
    #
    wi
    #
    vv
    cA
    wral
    #
    wa
    #
    vu
    cA
    wrex
    #
    vy
    cab
    #
    @32
    @20
    @4
    cG
    @51
    wcel
    #
    @7
    @20
    @52
    cG
    @39
    wcel
    #
    @42
    @38
    @14
    cres
    #
    @16
    wceq
    #
    wi
    #
    vv
    cA
    wral
    #
    wa
    #
    vu
    cA
    wrex
    #
    @20
    cG
    vp
    cv
    #
    cdm
    #
    wcel
    #
    @11
    @60
    cslt
    wbr
    #
    wn
    #
    @60
    @14
    cres
    #
    @16
    wceq
    #
    wi
    #
    vv
    cA
    wral
    #
    wa
    #
    vp
    cA
    wrex
    #
    @59
    @8
    @10
    @19
    @70
    @69
    @10
    @19
    wa
    vp
    cU
    cA
    @60
    cU
    wceq
    #
    @62
    @10
    @68
    @19
    @71
    @61
    @9
    cG
    @60
    cU
    dmeq
    eleq2d
    @71
    @67
    @18
    vv
    cA
    @71
    @64
    @13
    @66
    @17
    @71
    @63
    @12
    @60
    cU
    @11
    cslt
    breq2
    notbid
    @71
    @65
    @15
    @16
    @60
    cU
    @14
    reseq1
    eqeq1d
    imbi12d
    ralbidv
    anbi12d
    rspcev
    3impb
    @58
    @69
    vu
    vp
    cA
    vu
    vp
    weq
    #
    @53
    @62
    @57
    @68
    @72
    @39
    @61
    cG
    @38
    @60
    dmeq
    eleq2d
    @72
    @56
    @67
    vv
    cA
    @72
    @42
    @64
    @55
    @66
    @72
    @41
    @63
    @38
    @60
    @11
    cslt
    breq2
    notbid
    @72
    @54
    @65
    @16
    @38
    @60
    @14
    reseq1
    eqeq1d
    imbi12d
    ralbidv
    anbi12d
    cbvrexv
    sylibr
    @10
    @8
    @52
    @59
    wb
    @19
    @50
    @59
    vy
    cG
    @9
    @1
    cG
    wceq
    #
    @49
    @58
    vu
    cA
    @73
    @40
    @53
    @48
    @57
    @1
    cG
    @39
    eleq1
    @73
    @47
    @56
    vv
    cA
    @73
    @46
    @55
    @42
    @73
    @44
    @54
    @45
    @16
    @73
    @43
    @14
    @38
    @1
    cG
    suceq
    #
    reseq2d
    @73
    @43
    @14
    @11
    @74
    reseq2d
    eqeq12d
    imbi2d
    ralbidv
    anbi12d
    rexbidv
    elabg
    3ad2ant2
    mpbird
    3ad2ant3
    @4
    @7
    @32
    @51
    wceq
    @20
    @4
    @32
    vg
    @51
    vg
    cv
    #
    @39
    wcel
    @42
    @38
    @75
    csuc
    #
    cres
    @11
    @76
    cres
    wceq
    wi
    vv
    cA
    wral
    @75
    @38
    cfv
    @0
    wceq
    w3a
    vu
    cA
    wrex
    #
    vx
    cio
    #
    cmpt
    #
    cdm
    @51
    @4
    cS
    @79
    @4
    cS
    @3
    @2
    vx
    cA
    crio
    #
    @80
    cdm
    c2o
    cop
    csn
    cun
    #
    @79
    cif
    @79
    nosupres.1
    @3
    @81
    @79
    iffalse
    syl5eq
    dmeqd
    vg
    @51
    @78
    @79
    @77
    vx
    iotaex
    @79
    eqid
    dmmpti
    syl6eq
    3ad2ant1
    eleqtrrd
    cG
    @32
    ordsucss
    sylc
    @14
    @32
    df-ss
    sylib
    syl5eq
    #
    @21
    @25
    @14
    @9
    cin
    #
    @14
    cU
    @14
    dmres
    @21
    @14
    @9
    wss
    #
    @83
    @14
    wceq
    @21
    @9
    word
    #
    @10
    @84
    @21
    cU
    csur
    wcel
    #
    @85
    @21
    cA
    csur
    cU
    @4
    @5
    @6
    @20
    simp2l
    @4
    @7
    @8
    @10
    @19
    simp31
    sseldd
    #
    cU
    nodmord
    syl
    @4
    @7
    @8
    @10
    @19
    simp32
    #
    cG
    @9
    ordsucss
    sylc
    #
    @14
    @9
    df-ss
    sylib
    syl5eq
    eqtr4d
    @21
    @30
    va
    @24
    @21
    @27
    @24
    wcel
    @27
    @14
    wcel
    #
    @30
    @21
    @24
    @14
    @27
    @82
    eleq2d
    @21
    @90
    @30
    @21
    @90
    wa
    #
    @27
    cS
    cfv
    #
    @27
    cU
    cfv
    #
    @28
    @29
    @91
    @4
    @7
    @8
    @27
    @9
    wcel
    @13
    cU
    @27
    csuc
    #
    cres
    #
    @11
    @94
    cres
    #
    wceq
    #
    wi
    #
    vv
    cA
    wral
    #
    @92
    @93
    wceq
    @4
    @7
    @20
    @90
    simpl1
    @4
    @7
    @20
    @90
    simpl2
    @8
    @10
    @19
    @4
    @7
    @90
    simpl31
    @21
    @14
    @9
    @27
    @89
    sselda
    @91
    @94
    @14
    wss
    #
    @19
    @99
    @21
    @90
    @100
    @21
    @14
    word
    #
    @90
    @100
    wi
    @21
    cG
    word
    #
    @101
    @21
    cG
    con0
    wcel
    #
    @102
    @21
    @9
    con0
    wcel
    #
    @10
    @103
    @21
    @86
    @104
    @87
    cU
    nodmon
    syl
    @88
    @9
    cG
    onelon
    syl2anc
    cG
    eloni
    syl
    cG
    ordsuc
    sylib
    @27
    @14
    ordsucss
    syl
    imp
    @8
    @10
    @19
    @4
    @7
    @90
    simpl33
    @100
    @18
    @98
    vv
    cA
    @100
    @17
    @97
    @13
    @17
    @15
    @94
    cres
    #
    @16
    @94
    cres
    #
    wceq
    @100
    @97
    @15
    @16
    @94
    reseq1
    @100
    @105
    @95
    @106
    @96
    cU
    @94
    @14
    resabs1
    @11
    @94
    @14
    resabs1
    eqeq12d
    syl5ib
    imim2d
    ralimdv
    sylc
    vx
    vy
    vv
    vu
    cA
    cS
    cU
    vg
    @27
    nosupres.1
    nosupfv
    syl113anc
    @91
    @27
    @14
    cS
    @21
    @90
    simpr
    #
    fvresd
    @91
    @27
    @14
    cU
    @107
    fvresd
    3eqtr4d
    ex
    sylbid
    ralrimiv
    @21
    @22
    wfun
    #
    @15
    wfun
    #
    @23
    @26
    @31
    wa
    wb
    @21
    @36
    cS
    wfun
    @108
    @37
    cS
    nofun
    @14
    cS
    funres
    3syl
    @21
    @86
    cU
    wfun
    @109
    @87
    cU
    nofun
    @14
    cU
    funres
    3syl
    va
    @22
    @15
    eqfunfv
    syl2anc
    mpbir2and
end
