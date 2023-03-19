include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cbl.mm"
include "co.mm"
include "ciun.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "crp.mm"
include "wral.mm"
include "ctotbnd.mm"
include "cmpt.mm"
include "cprds.mm"
include "cds.mm"
include "cbs.mm"
include "cvv.mm"
include "eqid.mm"
include "wa.mm"
include "fvexd.mm"
include "totbndmet.mm"
include "syl.mm"
include "prdsmet.mm"
include "wfn.mm"
include "dffn5.mm"
include "sylib.mm"
include "oveq2d.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "3eltr4d.mm"
include "wf.mm"
include "wex.mm"
include "adantr.mm"
include "istotbnd3.mm"
include "simprbi.mm"
include "r19.21bi.mm"
include "df-rex.mm"
include "rexv.mm"
include "bitr4i.mm"
include "an32s.mm"
include "ralrimiva.mm"
include "eleq1.mm"
include "iuneq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "ac6sfi.mm"
include "syl2anc.mm"
include "cixp.mm"
include "wss.mm"
include "elfpw.mm"
include "simplbi.mm"
include "ralimi.mm"
include "ad2antll.mm"
include "ss2ixp.mm"
include "fnfi.mm"
include "cdm.mm"
include "fndm.mm"
include "prdsbas.mm"
include "rgenw.mm"
include "ixpeq2.mm"
include "ax-mp.mm"
include "syl6eqr.mm"
include "ad2antrr.mm"
include "sseqtr4d.mm"
include "ixpfi.mm"
include "sylanbrc.mm"
include "cxmt.mm"
include "cxr.mm"
include "metxmet.mm"
include "rpxr.mm"
include "blssm.mm"
include "3expa.mm"
include "syl2an.mm"
include "ssralv.mm"
include "sylc.mm"
include "iunss.mm"
include "sylibr.mm"
include "eleq2d.mm"
include "vex.mm"
include "elixp.mm"
include "wi.mm"
include "eliun.mm"
include "3bitr4i.mm"
include "eleq2.mm"
include "syl5bbr.mm"
include "biimprd.mm"
include "adantl.mm"
include "ral2imi.mm"
include "syl5.mm"
include "sylbid.mm"
include "imp.mm"
include "oveq1.mm"
include "ffn.mm"
include "simpl.mm"
include "anim12i.mm"
include "biimpa.mm"
include "ixpfn.mm"
include "simpr.mm"
include "simp-4l.mm"
include "sseldd.mm"
include "eleqtrrd.mm"
include "simp-4r.mm"
include "fveq2.mm"
include "cbvmptv.mm"
include "oveq2i.mm"
include "oveqdr.mm"
include "adantlr.mm"
include "simprl.mm"
include "eleqtrd.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "rpgt0.mm"
include "prdsbl.mm"
include "eqtrd.mm"
include "syl12anc.mm"
include "jca.mm"
include "ex.mm"
include "eximdv.mm"
include "syl6ibr.mm"
include "mpd.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "rspcev.mm"
include "exlimddv.mm"

theorem prdstotbnd
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let cE: class E
  let cI: class I
  let cV: class V
  let cW: class W
  let cY: class Y
  let vz: setvar z
  let va: setvar a
  let vr: setvar r
  let cA: class A
  let cC: class C
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vm: setvar m
  let vv: setvar v
  let vy: setvar y
  let vw: setvar w
  assume prdsbnd.y: |- Y = ( S Xs_ R )
  assume prdsbnd.b: |- B = ( Base ` Y )
  assume prdsbnd.v: |- V = ( Base ` ( R ` x ) )
  assume prdsbnd.e: |- E = ( ( dist ` ( R ` x ) ) |` ( V X. V ) )
  assume prdsbnd.d: |- D = ( dist ` Y )
  assume prdsbnd.s: |- ( ph -> S e. W )
  assume prdsbnd.i: |- ( ph -> I e. Fin )
  assume prdsbnd.r: |- ( ph -> R Fn I )
  assume prdstotbnd.m: |- ( ( ph /\ x e. I ) -> E e. ( TotBnd ` V ) )

  disjoint R x
  disjoint B x
  disjoint ph x
  disjoint I x
  disjoint S x
  disjoint Y x
  disjoint x z
  disjoint a r
  disjoint a z
  disjoint A a
  disjoint r z
  disjoint A r
  disjoint A z
  disjoint C a
  disjoint C r
  disjoint C z
  disjoint f g
  disjoint f k
  disjoint f m
  disjoint f r
  disjoint f v
  disjoint f y
  disjoint D f
  disjoint g k
  disjoint g m
  disjoint g r
  disjoint g v
  disjoint g y
  disjoint D g
  disjoint k m
  disjoint k r
  disjoint k v
  disjoint k y
  disjoint D k
  disjoint m r
  disjoint m v
  disjoint m y
  disjoint D m
  disjoint r v
  disjoint r y
  disjoint D r
  disjoint v y
  disjoint D v
  disjoint D y
  disjoint x y
  disjoint R y
  disjoint f w
  disjoint f x
  disjoint B f
  disjoint g w
  disjoint g x
  disjoint B g
  disjoint k w
  disjoint k x
  disjoint B k
  disjoint m w
  disjoint m x
  disjoint B m
  disjoint r w
  disjoint r x
  disjoint B r
  disjoint v w
  disjoint v x
  disjoint B v
  disjoint w x
  disjoint w y
  disjoint B w
  disjoint B y
  disjoint f z
  disjoint E f
  disjoint g z
  disjoint E g
  disjoint k z
  disjoint E k
  disjoint E r
  disjoint w z
  disjoint E w
  disjoint y z
  disjoint E y
  disjoint E z
  disjoint a f
  disjoint a g
  disjoint a k
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a ph
  disjoint f ph
  disjoint g ph
  disjoint k ph
  disjoint ph r
  disjoint ph w
  disjoint ph y
  disjoint I f
  disjoint I g
  disjoint I k
  disjoint I v
  disjoint I w
  disjoint I y
  disjoint V f
  disjoint V g
  disjoint V k
  disjoint V r
  disjoint V w
  disjoint V y
  disjoint V z
  assert |- ( ph -> D e. ( TotBnd ` B ) )

  proof
    wph
    cD
    cB
    cme
    cfv
    #
    wcel
    #
    vy
    vv
    cv
    #
    vy
    cv
    #
    vr
    cv
    #
    cD
    cbl
    cfv
    #
    co
    #
    ciun
    #
    cB
    wceq
    #
    vv
    cB
    cpw
    cfn
    cin
    #
    wrex
    #
    vr
    crp
    wral
    cD
    cB
    ctotbnd
    cfv
    wcel
    wph
    cS
    vx
    cI
    vx
    cv
    #
    cR
    cfv
    #
    cmpt
    #
    cprds
    co
    #
    cds
    cfv
    #
    @14
    cbs
    cfv
    #
    cme
    cfv
    cD
    @0
    wph
    vx
    @16
    @15
    @12
    cS
    cE
    cI
    cV
    cW
    @14
    cvv
    @14
    eqid
    @16
    eqid
    prdsbnd.v
    prdsbnd.e
    @15
    eqid
    prdsbnd.s
    prdsbnd.i
    wph
    @11
    cI
    wcel
    #
    wa
    #
    @11
    cR
    fvexd
    @18
    cE
    cV
    ctotbnd
    cfv
    wcel
    #
    cE
    cV
    cme
    cfv
    wcel
    #
    prdstotbnd.m
    cE
    cV
    totbndmet
    syl
    #
    prdsmet
    wph
    cD
    cY
    cds
    cfv
    #
    @15
    prdsbnd.d
    wph
    cY
    @14
    cds
    wph
    cY
    cS
    cR
    cprds
    co
    @14
    prdsbnd.y
    wph
    cR
    @13
    cS
    cprds
    wph
    cR
    cI
    wfn
    #
    cR
    @13
    wceq
    prdsbnd.r
    vx
    cI
    cR
    dffn5
    sylib
    oveq2d
    syl5eq
    #
    fveq2d
    syl5eq
    wph
    cB
    @16
    cme
    wph
    cB
    cY
    cbs
    cfv
    #
    @16
    prdsbnd.b
    wph
    cY
    @14
    cbs
    @24
    fveq2d
    syl5eq
    fveq2d
    3eltr4d
    #
    wph
    @10
    vr
    crp
    wph
    @4
    crp
    wcel
    #
    wa
    #
    cI
    cvv
    vf
    cv
    #
    wf
    #
    @11
    @29
    cfv
    #
    cV
    cpw
    cfn
    cin
    #
    wcel
    #
    vz
    @31
    vz
    cv
    #
    @4
    cE
    cbl
    cfv
    #
    co
    #
    ciun
    #
    cV
    wceq
    #
    wa
    #
    vx
    cI
    wral
    #
    wa
    #
    @10
    vf
    @28
    cI
    cfn
    wcel
    #
    vw
    cv
    #
    @32
    wcel
    #
    vz
    @43
    @36
    ciun
    #
    cV
    wceq
    #
    wa
    #
    vw
    cvv
    wrex
    #
    vx
    cI
    wral
    @41
    vf
    wex
    wph
    @42
    @27
    prdsbnd.i
    adantr
    #
    @28
    @48
    vx
    cI
    wph
    @17
    @27
    @48
    @18
    @27
    wa
    @46
    vw
    @32
    wrex
    #
    @48
    @18
    @50
    vr
    crp
    @18
    @19
    @50
    vr
    crp
    wral
    #
    prdstotbnd.m
    @19
    @20
    @51
    vz
    vw
    cE
    cV
    vr
    istotbnd3
    simprbi
    syl
    r19.21bi
    @50
    @47
    vw
    wex
    @48
    @46
    vw
    @32
    df-rex
    @47
    vw
    rexv
    bitr4i
    sylib
    an32s
    ralrimiva
    @47
    @39
    vx
    vw
    cI
    cvv
    vf
    @43
    @31
    wceq
    #
    @44
    @33
    @46
    @38
    @43
    @31
    @32
    eleq1
    @52
    @45
    @37
    cV
    vz
    @43
    @31
    @36
    iuneq1
    eqeq1d
    anbi12d
    ac6sfi
    syl2anc
    @28
    @41
    wa
    #
    vx
    cI
    @31
    cixp
    #
    @9
    wcel
    #
    vy
    @54
    @6
    ciun
    #
    cB
    wceq
    #
    @10
    @53
    @54
    cB
    wss
    #
    @54
    cfn
    wcel
    #
    @55
    @53
    @54
    vx
    cI
    cV
    cixp
    #
    cB
    @53
    @31
    cV
    wss
    #
    vx
    cI
    wral
    #
    @54
    @60
    wss
    #
    @40
    @62
    @28
    @30
    @39
    @61
    vx
    cI
    @33
    @61
    @38
    @33
    @61
    @31
    cfn
    wcel
    #
    @31
    cV
    elfpw
    #
    simplbi
    adantr
    ralimi
    ad2antll
    vx
    cI
    @31
    cV
    ss2ixp
    syl
    #
    wph
    cB
    @60
    wceq
    #
    @27
    @41
    wph
    cB
    vx
    cI
    @12
    cbs
    cfv
    #
    cixp
    #
    @60
    wph
    vx
    cB
    cY
    cR
    cS
    cI
    cW
    cfn
    prdsbnd.y
    prdsbnd.s
    wph
    @23
    @42
    cR
    cfn
    wcel
    prdsbnd.r
    prdsbnd.i
    cI
    cR
    fnfi
    syl2anc
    prdsbnd.b
    wph
    @23
    cR
    cdm
    cI
    wceq
    prdsbnd.r
    cI
    cR
    fndm
    syl
    prdsbas
    cV
    @68
    wceq
    #
    vx
    cI
    wral
    @60
    @69
    wceq
    @70
    vx
    cI
    prdsbnd.v
    rgenw
    vx
    cI
    cV
    @68
    ixpeq2
    ax-mp
    syl6eqr
    #
    ad2antrr
    #
    sseqtr4d
    #
    @53
    @42
    @64
    vx
    cI
    wral
    #
    @59
    @28
    @42
    @41
    @49
    adantr
    #
    @40
    @74
    @28
    @30
    @39
    @64
    vx
    cI
    @33
    @64
    @38
    @33
    @61
    @64
    @65
    simprbi
    adantr
    ralimi
    ad2antll
    vx
    cI
    @31
    ixpfi
    syl2anc
    @54
    cB
    elfpw
    sylanbrc
    @53
    @56
    cB
    @53
    @6
    cB
    wss
    #
    vy
    @54
    wral
    #
    @56
    cB
    wss
    @53
    @58
    @76
    vy
    cB
    wral
    #
    @77
    @73
    @28
    @78
    @41
    wph
    cD
    cB
    cxmt
    cfv
    wcel
    #
    @4
    cxr
    wcel
    #
    @78
    @27
    wph
    @1
    @79
    @26
    cD
    cB
    metxmet
    syl
    @4
    rpxr
    #
    @79
    @80
    wa
    @76
    vy
    cB
    @79
    @3
    cB
    wcel
    #
    @80
    @76
    @79
    @82
    @80
    @76
    cD
    @3
    @4
    cB
    blssm
    3expa
    an32s
    ralrimiva
    syl2an
    adantr
    @76
    vy
    @54
    cB
    ssralv
    sylc
    vy
    @54
    @6
    cB
    iunss
    sylibr
    @53
    vg
    cB
    @56
    @53
    vg
    cv
    #
    cB
    wcel
    #
    @83
    @6
    wcel
    #
    vy
    @54
    wrex
    #
    @83
    @56
    wcel
    @53
    @84
    @86
    @53
    @84
    wa
    #
    cI
    cvv
    @3
    wf
    #
    @11
    @3
    cfv
    #
    @31
    wcel
    #
    @11
    @83
    cfv
    #
    @89
    @4
    @35
    co
    #
    wcel
    #
    wa
    #
    vx
    cI
    wral
    #
    wa
    #
    vy
    wex
    #
    @86
    @87
    @42
    @34
    @31
    wcel
    #
    @91
    @36
    wcel
    #
    wa
    #
    vz
    cvv
    wrex
    #
    vx
    cI
    wral
    #
    @97
    @53
    @42
    @84
    @75
    adantr
    @53
    @84
    @102
    @53
    @84
    @83
    @60
    wcel
    #
    @102
    @53
    cB
    @60
    @83
    @72
    eleq2d
    #
    @103
    @91
    cV
    wcel
    #
    vx
    cI
    wral
    #
    @53
    @102
    @103
    @83
    cI
    wfn
    #
    @106
    vx
    cI
    cV
    @83
    vg
    vex
    #
    elixp
    simprbi
    @40
    @106
    @102
    wi
    @28
    @30
    @39
    @105
    @101
    vx
    cI
    @38
    @105
    @101
    wi
    @33
    @38
    @101
    @105
    @101
    @91
    @37
    wcel
    #
    @38
    @105
    @99
    vz
    @31
    wrex
    @100
    vz
    wex
    @109
    @101
    @99
    vz
    @31
    df-rex
    vz
    @91
    @31
    @36
    eliun
    @100
    vz
    rexv
    3bitr4i
    @37
    cV
    @91
    eleq2
    syl5bbr
    biimprd
    adantl
    ral2imi
    ad2antll
    syl5
    sylbid
    imp
    @100
    @94
    vx
    vz
    cI
    cvv
    vy
    @34
    @89
    wceq
    #
    @98
    @90
    @99
    @93
    @34
    @89
    @31
    eleq1
    @110
    @36
    @92
    @91
    @34
    @89
    @4
    @35
    oveq1
    eleq2d
    anbi12d
    ac6sfi
    syl2anc
    @87
    @97
    @3
    @54
    wcel
    #
    @85
    wa
    #
    vy
    wex
    @86
    @87
    @96
    @112
    vy
    @87
    @96
    @112
    @87
    @96
    wa
    #
    @111
    @85
    @96
    @111
    @87
    @96
    @3
    cI
    wfn
    #
    @90
    vx
    cI
    wral
    #
    wa
    @111
    @88
    @114
    @95
    @115
    cI
    cvv
    @3
    ffn
    @94
    @90
    vx
    cI
    @90
    @93
    simpl
    ralimi
    anim12i
    vx
    cI
    @31
    @3
    vy
    vex
    elixp
    sylibr
    adantl
    #
    @113
    @83
    vx
    cI
    @92
    cixp
    #
    @6
    @113
    @107
    @93
    vx
    cI
    wral
    #
    @83
    @117
    wcel
    @87
    @107
    @96
    @87
    @103
    @107
    @53
    @84
    @103
    @104
    biimpa
    vx
    cI
    cV
    @83
    ixpfn
    syl
    adantr
    @95
    @118
    @87
    @88
    @94
    @93
    vx
    cI
    @90
    @93
    simpr
    ralimi
    ad2antll
    vx
    cI
    @92
    @83
    @108
    elixp
    sylanbrc
    @113
    wph
    @82
    @27
    @6
    @117
    wceq
    wph
    @27
    @41
    @84
    @96
    simp-4l
    #
    @113
    @3
    @60
    cB
    @113
    @54
    @60
    @3
    @53
    @63
    @84
    @96
    @66
    ad2antrr
    @116
    sseldd
    @113
    wph
    @67
    @119
    @71
    syl
    eleqtrrd
    wph
    @27
    @41
    @84
    @96
    simp-4r
    wph
    @82
    @27
    wa
    #
    wa
    #
    @6
    @3
    @4
    cS
    vy
    cI
    @3
    cR
    cfv
    #
    cmpt
    #
    cprds
    co
    #
    cds
    cfv
    #
    cbl
    cfv
    #
    co
    @117
    wph
    @120
    vy
    vr
    @5
    @126
    wph
    cD
    @125
    cbl
    wph
    cD
    @22
    @125
    prdsbnd.d
    wph
    cY
    @124
    cds
    wph
    cY
    @14
    @124
    @24
    @123
    @13
    cS
    cprds
    vy
    vx
    cI
    @122
    @12
    @3
    @11
    cR
    fveq2
    cbvmptv
    oveq2i
    #
    syl6eqr
    #
    fveq2d
    syl5eq
    fveq2d
    oveqdr
    @121
    vx
    @4
    @124
    cbs
    cfv
    #
    @125
    @3
    @12
    cS
    cE
    cI
    cV
    cW
    @124
    cvv
    @127
    @129
    eqid
    prdsbnd.v
    prdsbnd.e
    @125
    eqid
    wph
    cS
    cW
    wcel
    @120
    prdsbnd.s
    adantr
    wph
    @42
    @120
    prdsbnd.i
    adantr
    @121
    @17
    wa
    @11
    cR
    fvexd
    wph
    @17
    cE
    cV
    cxmt
    cfv
    wcel
    #
    @120
    @18
    @20
    @130
    @21
    cE
    cV
    metxmet
    syl
    adantlr
    @121
    @3
    cB
    @129
    wph
    @82
    @27
    simprl
    wph
    cB
    @129
    wceq
    @120
    wph
    cB
    @25
    @129
    prdsbnd.b
    wph
    cY
    @124
    cbs
    @128
    fveq2d
    syl5eq
    adantr
    eleqtrd
    @27
    @80
    wph
    @82
    @81
    ad2antll
    @27
    cc0
    @4
    clt
    wbr
    wph
    @82
    @4
    rpgt0
    ad2antll
    prdsbl
    eqtrd
    syl12anc
    eleqtrrd
    jca
    ex
    eximdv
    @85
    vy
    @54
    df-rex
    syl6ibr
    mpd
    ex
    vy
    @83
    @54
    @6
    eliun
    syl6ibr
    ssrdv
    eqssd
    @8
    @57
    vv
    @54
    @9
    @2
    @54
    wceq
    @7
    @56
    cB
    vy
    @2
    @54
    @6
    iuneq1
    eqeq1d
    rspcev
    syl2anc
    exlimddv
    ralrimiva
    vy
    vv
    cD
    cB
    vr
    istotbnd3
    sylanbrc
end
