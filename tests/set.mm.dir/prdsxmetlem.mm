include "cvv.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "cxp.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "cxr.mm"
include "wss.mm"
include "prdsdsf.mm"
include "iccssxr.mm"
include "fss.mm"
include "sylancl.mm"
include "cv.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "fovrnda.mm"
include "elxrge0.mm"
include "simprbi.mm"
include "syl.mm"
include "cmpt.mm"
include "crn.mm"
include "csn.mm"
include "cun.mm"
include "clt.mm"
include "csup.mm"
include "wral.mm"
include "wceq.mm"
include "adantr.mm"
include "ralrimiva.mm"
include "simprl.mm"
include "simprr.mm"
include "prdsdsval3.mm"
include "breq1d.mm"
include "wb.mm"
include "cxmt.mm"
include "adantlr.mm"
include "prdsbascl.mm"
include "r19.21bi.mm"
include "xmetcl.mm"
include "syl3anc.mm"
include "eqid.mm"
include "fmptd.mm"
include "frn.mm"
include "0xr.mm"
include "snssd.mm"
include "unssd.mm"
include "supxrleub.mm"
include "0le0.mm"
include "c0ex.mm"
include "breq1.mm"
include "ralsn.mm"
include "mpbir.mm"
include "ralunb.mm"
include "mpbiran2.mm"
include "ovex.mm"
include "rgenw.mm"
include "ralrnmpt.mm"
include "ax-mp.mm"
include "bitri.mm"
include "xmetge0.mm"
include "biantrud.mm"
include "xrletri3.mm"
include "xmeteq0.mm"
include "3bitr2d.mm"
include "ralbidva.mm"
include "wfn.mm"
include "fnmpt.mm"
include "prdsbasfn.mm"
include "eqfnfv.mm"
include "syl2anc.mm"
include "bitr4d.mm"
include "syl5bb.mm"
include "3bitrd.mm"
include "w3a.mm"
include "cr.mm"
include "caddc.mm"
include "3adantr3.mm"
include "3adant3.mm"
include "3ad2antl1.mm"
include "3ad2ant1.mm"
include "simp23.mm"
include "simp3l.mm"
include "ssun1.mm"
include "wrex.mm"
include "cab.mm"
include "elabrex.mm"
include "adantl.mm"
include "rnmpt.mm"
include "syl6eleqr.mm"
include "sseldi.mm"
include "supxrub.mm"
include "simp21.mm"
include "breqtrrd.mm"
include "xrrege0.mm"
include "syl22anc.mm"
include "simp3r.mm"
include "simp22.mm"
include "readdcld.mm"
include "cxad.mm"
include "xmettri2.mm"
include "syl13anc.mm"
include "rexadd.mm"
include "breqtrd.mm"
include "readdcl.mm"
include "3ad2ant3.mm"
include "le2addd.mm"
include "letrd.mm"
include "mpbird.mm"
include "fovrnd.mm"
include "addge0d.mm"
include "sylibr.mm"
include "sylanbrc.mm"
include "rexrd.mm"
include "eqbrtrd.mm"
include "isxmet2d.mm"

theorem prdsxmetlem
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
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vy: setvar y
  let vz: setvar z
  assume prdsdsf.y: |- Y = ( S Xs_ ( x e. I |-> R ) )
  assume prdsdsf.b: |- B = ( Base ` Y )
  assume prdsdsf.v: |- V = ( Base ` R )
  assume prdsdsf.e: |- E = ( ( dist ` R ) |` ( V X. V ) )
  assume prdsdsf.d: |- D = ( dist ` Y )
  assume prdsdsf.s: |- ( ph -> S e. W )
  assume prdsdsf.i: |- ( ph -> I e. X )
  assume prdsdsf.r: |- ( ( ph /\ x e. I ) -> R e. Z )
  assume prdsdsf.m: |- ( ( ph /\ x e. I ) -> E e. ( *Met ` V ) )

  disjoint B x
  disjoint D x
  disjoint I x
  disjoint ph x
  disjoint f g
  disjoint f h
  disjoint f y
  disjoint B f
  disjoint g h
  disjoint g y
  disjoint B g
  disjoint h y
  disjoint B h
  disjoint B y
  disjoint f z
  disjoint D f
  disjoint g z
  disjoint D g
  disjoint h z
  disjoint D h
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint E z
  disjoint f x
  disjoint I f
  disjoint g x
  disjoint I g
  disjoint x y
  disjoint x z
  disjoint I y
  disjoint I z
  disjoint V z
  disjoint f ph
  disjoint g ph
  disjoint h x
  disjoint h ph
  disjoint ph y
  disjoint R f
  disjoint R g
  disjoint R y
  disjoint R z
  disjoint S f
  disjoint S g
  disjoint S y
  disjoint Y f
  disjoint Y g
  disjoint Y y
  assert |- ( ph -> D e. ( *Met ` B ) )

  proof
    wph
    vf
    vg
    vh
    cD
    cB
    cB
    cvv
    wcel
    wph
    cB
    cY
    cbs
    cfv
    cvv
    prdsdsf.b
    cY
    cbs
    fvex
    eqeltri
    a1i
    wph
    cB
    cB
    cxp
    #
    cc0
    cpnf
    cicc
    co
    #
    cD
    wf
    #
    @1
    cxr
    wss
    @0
    cxr
    cD
    wf
    wph
    vx
    cB
    cD
    cR
    cS
    cE
    cI
    cV
    cW
    cX
    cY
    cZ
    prdsdsf.y
    prdsdsf.b
    prdsdsf.v
    prdsdsf.e
    prdsdsf.d
    prdsdsf.s
    prdsdsf.i
    prdsdsf.r
    prdsdsf.m
    prdsdsf
    #
    cc0
    cpnf
    iccssxr
    @0
    @1
    cxr
    cD
    fss
    sylancl
    wph
    vf
    cv
    #
    cB
    wcel
    #
    vg
    cv
    #
    cB
    wcel
    #
    wa
    #
    wa
    #
    @4
    @6
    cD
    co
    #
    @1
    wcel
    #
    cc0
    @10
    cle
    wbr
    #
    wph
    @4
    @6
    @1
    cB
    cB
    cD
    @3
    fovrnda
    @11
    @10
    cxr
    wcel
    @12
    @10
    elxrge0
    simprbi
    syl
    @9
    @10
    cc0
    cle
    wbr
    vx
    cI
    vx
    cv
    #
    @4
    cfv
    #
    @13
    @6
    cfv
    #
    cE
    co
    #
    cmpt
    #
    crn
    #
    cc0
    csn
    #
    cun
    #
    cxr
    clt
    csup
    #
    cc0
    cle
    wbr
    #
    vz
    cv
    #
    cc0
    cle
    wbr
    #
    vz
    @20
    wral
    #
    @4
    @6
    wceq
    #
    @9
    @10
    @21
    cc0
    cle
    @9
    vx
    cB
    cD
    cR
    cS
    cE
    @4
    @6
    cI
    cV
    cW
    cX
    cZ
    cY
    prdsdsf.y
    prdsdsf.b
    wph
    cS
    cW
    wcel
    #
    @8
    prdsdsf.s
    adantr
    #
    wph
    cI
    cX
    wcel
    #
    @8
    prdsdsf.i
    adantr
    #
    wph
    cR
    cZ
    wcel
    #
    vx
    cI
    wral
    #
    @8
    wph
    @31
    vx
    cI
    prdsdsf.r
    ralrimiva
    #
    adantr
    #
    wph
    @5
    @7
    simprl
    #
    wph
    @5
    @7
    simprr
    #
    prdsdsf.v
    prdsdsf.e
    prdsdsf.d
    prdsdsval3
    #
    breq1d
    @9
    @20
    cxr
    wss
    #
    cc0
    cxr
    wcel
    #
    @22
    @25
    wb
    @9
    @18
    @19
    cxr
    @9
    cI
    cxr
    @17
    wf
    @18
    cxr
    wss
    @9
    vx
    cI
    @16
    cxr
    @17
    @9
    @13
    cI
    wcel
    #
    wa
    #
    cE
    cV
    cxmt
    cfv
    wcel
    #
    @14
    cV
    wcel
    #
    @15
    cV
    wcel
    #
    @16
    cxr
    wcel
    #
    wph
    @40
    @42
    @8
    prdsdsf.m
    adantlr
    #
    @9
    @43
    vx
    cI
    @9
    vx
    cB
    cR
    cS
    @4
    cI
    cV
    cW
    cX
    cZ
    cY
    prdsdsf.y
    prdsdsf.b
    @28
    @30
    @34
    prdsdsf.v
    @35
    prdsbascl
    #
    r19.21bi
    #
    @9
    @44
    vx
    cI
    @9
    vx
    cB
    cR
    cS
    @6
    cI
    cV
    cW
    cX
    cZ
    cY
    prdsdsf.y
    prdsdsf.b
    @28
    @30
    @34
    prdsdsf.v
    @36
    prdsbascl
    #
    r19.21bi
    #
    @14
    @15
    cE
    cV
    xmetcl
    #
    syl3anc
    #
    @17
    eqid
    #
    fmptd
    cI
    cxr
    @17
    frn
    syl
    @9
    cc0
    cxr
    @39
    @9
    0xr
    a1i
    snssd
    unssd
    #
    0xr
    vz
    @20
    cc0
    supxrleub
    sylancl
    @25
    @16
    cc0
    cle
    wbr
    #
    vx
    cI
    wral
    #
    @9
    @26
    @25
    @24
    vz
    @18
    wral
    #
    @56
    @25
    @57
    @24
    vz
    @19
    wral
    #
    @58
    cc0
    cc0
    cle
    wbr
    #
    0le0
    @24
    @59
    vz
    cc0
    c0ex
    @23
    cc0
    cc0
    cle
    breq1
    ralsn
    mpbir
    @24
    vz
    @18
    @19
    ralunb
    mpbiran2
    @16
    cvv
    wcel
    #
    vx
    cI
    wral
    @57
    @56
    wb
    @60
    vx
    cI
    @14
    @15
    cE
    ovex
    rgenw
    @24
    @55
    vx
    vz
    cI
    @16
    @17
    cvv
    @53
    @23
    @16
    cc0
    cle
    breq1
    ralrnmpt
    ax-mp
    bitri
    @9
    @56
    @14
    @15
    wceq
    #
    vx
    cI
    wral
    #
    @26
    @9
    @55
    @61
    vx
    cI
    @41
    @55
    @55
    cc0
    @16
    cle
    wbr
    #
    wa
    #
    @16
    cc0
    wceq
    #
    @61
    @41
    @63
    @55
    @41
    @42
    @43
    @44
    @63
    @46
    @48
    @50
    @14
    @15
    cE
    cV
    xmetge0
    #
    syl3anc
    biantrud
    @41
    @45
    @39
    @65
    @64
    wb
    @52
    0xr
    @16
    cc0
    xrletri3
    sylancl
    @41
    @42
    @43
    @44
    @65
    @61
    wb
    @46
    @48
    @50
    @14
    @15
    cE
    cV
    xmeteq0
    syl3anc
    3bitr2d
    ralbidva
    @9
    @4
    cI
    wfn
    @6
    cI
    wfn
    @26
    @62
    wb
    @9
    cB
    vx
    cI
    cR
    cmpt
    #
    cS
    @4
    cI
    cW
    cX
    cY
    prdsdsf.y
    prdsdsf.b
    @28
    @30
    wph
    @67
    cI
    wfn
    #
    @8
    wph
    @32
    @68
    @33
    vx
    cI
    cR
    @67
    cZ
    @67
    eqid
    fnmpt
    syl
    adantr
    #
    @35
    prdsbasfn
    @9
    cB
    @67
    cS
    @6
    cI
    cW
    cX
    cY
    prdsdsf.y
    prdsdsf.b
    @28
    @30
    @69
    @36
    prdsbasfn
    vx
    cI
    @4
    @6
    eqfnfv
    syl2anc
    bitr4d
    syl5bb
    3bitrd
    wph
    @5
    @7
    vh
    cv
    #
    cB
    wcel
    #
    w3a
    #
    @70
    @4
    cD
    co
    #
    cr
    wcel
    #
    @70
    @6
    cD
    co
    #
    cr
    wcel
    #
    wa
    #
    w3a
    #
    @10
    @21
    @73
    @75
    caddc
    co
    #
    cle
    wph
    @72
    @10
    @21
    wceq
    #
    @77
    wph
    @5
    @7
    @80
    @71
    @37
    3adantr3
    3adant3
    @78
    @21
    @79
    cle
    wbr
    #
    @23
    @79
    cle
    wbr
    #
    vz
    @20
    wral
    #
    @78
    @82
    vz
    @18
    wral
    #
    @82
    vz
    @19
    wral
    #
    @83
    @78
    @84
    @16
    @79
    cle
    wbr
    #
    vx
    cI
    wral
    #
    @78
    @86
    vx
    cI
    @78
    @40
    wa
    #
    @16
    @13
    @70
    cfv
    #
    @14
    cE
    co
    #
    @89
    @15
    cE
    co
    #
    caddc
    co
    #
    @79
    @88
    @45
    @92
    cr
    wcel
    @63
    @16
    @92
    cle
    wbr
    @16
    cr
    wcel
    @88
    @42
    @43
    @44
    @45
    wph
    @72
    @40
    @42
    @77
    prdsdsf.m
    3ad2antl1
    #
    @78
    @43
    vx
    cI
    wph
    @72
    @43
    vx
    cI
    wral
    #
    @77
    wph
    @5
    @7
    @94
    @71
    @47
    3adantr3
    3adant3
    r19.21bi
    #
    @78
    @44
    vx
    cI
    wph
    @72
    @44
    vx
    cI
    wral
    #
    @77
    wph
    @5
    @7
    @96
    @71
    @49
    3adantr3
    3adant3
    r19.21bi
    #
    @51
    syl3anc
    #
    @88
    @90
    @91
    @88
    @90
    cxr
    wcel
    #
    @74
    cc0
    @90
    cle
    wbr
    #
    @90
    @73
    cle
    wbr
    @90
    cr
    wcel
    #
    @88
    @42
    @89
    cV
    wcel
    #
    @43
    @99
    @93
    @78
    @102
    vx
    cI
    @78
    vx
    cB
    cR
    cS
    @70
    cI
    cV
    cW
    cX
    cZ
    cY
    prdsdsf.y
    prdsdsf.b
    wph
    @72
    @27
    @77
    prdsdsf.s
    3ad2ant1
    #
    wph
    @72
    @29
    @77
    prdsdsf.i
    3ad2ant1
    #
    wph
    @72
    @32
    @77
    @33
    3ad2ant1
    #
    prdsdsf.v
    wph
    @5
    @7
    @71
    @77
    simp23
    #
    prdsbascl
    r19.21bi
    #
    @95
    @89
    @14
    cE
    cV
    xmetcl
    syl3anc
    #
    @78
    @74
    @40
    wph
    @72
    @74
    @76
    simp3l
    #
    adantr
    #
    @88
    @42
    @102
    @43
    @100
    @93
    @107
    @95
    @89
    @14
    cE
    cV
    xmetge0
    syl3anc
    @88
    @90
    vx
    cI
    @90
    cmpt
    #
    crn
    #
    @19
    cun
    #
    cxr
    clt
    csup
    #
    @73
    cle
    @88
    @113
    cxr
    wss
    #
    @90
    @113
    wcel
    @90
    @114
    cle
    wbr
    @78
    @115
    @40
    @78
    @112
    @19
    cxr
    @78
    cI
    cxr
    @111
    wf
    @112
    cxr
    wss
    @78
    vx
    cI
    @90
    cxr
    @111
    @108
    @111
    eqid
    #
    fmptd
    cI
    cxr
    @111
    frn
    syl
    @78
    cc0
    cxr
    @39
    @78
    0xr
    a1i
    snssd
    #
    unssd
    adantr
    @88
    @112
    @113
    @90
    @112
    @19
    ssun1
    @88
    @90
    @23
    @90
    wceq
    vx
    cI
    wrex
    vz
    cab
    #
    @112
    @40
    @90
    @118
    wcel
    @78
    vx
    vz
    cI
    @90
    @89
    @14
    cE
    ovex
    elabrex
    adantl
    vx
    vz
    cI
    @90
    @111
    @116
    rnmpt
    syl6eleqr
    sseldi
    @113
    @90
    supxrub
    syl2anc
    @78
    @73
    @114
    wceq
    @40
    @78
    vx
    cB
    cD
    cR
    cS
    cE
    @70
    @4
    cI
    cV
    cW
    cX
    cZ
    cY
    prdsdsf.y
    prdsdsf.b
    @103
    @104
    @105
    @106
    wph
    @5
    @7
    @71
    @77
    simp21
    #
    prdsdsf.v
    prdsdsf.e
    prdsdsf.d
    prdsdsval3
    adantr
    breqtrrd
    #
    @90
    @73
    xrrege0
    syl22anc
    #
    @88
    @91
    cxr
    wcel
    #
    @76
    cc0
    @91
    cle
    wbr
    #
    @91
    @75
    cle
    wbr
    @91
    cr
    wcel
    #
    @88
    @42
    @102
    @44
    @122
    @93
    @107
    @97
    @89
    @15
    cE
    cV
    xmetcl
    syl3anc
    #
    @78
    @76
    @40
    wph
    @72
    @74
    @76
    simp3r
    #
    adantr
    #
    @88
    @42
    @102
    @44
    @123
    @93
    @107
    @97
    @89
    @15
    cE
    cV
    xmetge0
    syl3anc
    @88
    @91
    vx
    cI
    @91
    cmpt
    #
    crn
    #
    @19
    cun
    #
    cxr
    clt
    csup
    #
    @75
    cle
    @88
    @130
    cxr
    wss
    #
    @91
    @130
    wcel
    @91
    @131
    cle
    wbr
    @78
    @132
    @40
    @78
    @129
    @19
    cxr
    @78
    cI
    cxr
    @128
    wf
    @129
    cxr
    wss
    @78
    vx
    cI
    @91
    cxr
    @128
    @125
    @128
    eqid
    #
    fmptd
    cI
    cxr
    @128
    frn
    syl
    @117
    unssd
    adantr
    @88
    @129
    @130
    @91
    @129
    @19
    ssun1
    @88
    @91
    @23
    @91
    wceq
    vx
    cI
    wrex
    vz
    cab
    #
    @129
    @40
    @91
    @134
    wcel
    @78
    vx
    vz
    cI
    @91
    @89
    @15
    cE
    ovex
    elabrex
    adantl
    vx
    vz
    cI
    @91
    @128
    @133
    rnmpt
    syl6eleqr
    sseldi
    @130
    @91
    supxrub
    syl2anc
    @78
    @75
    @131
    wceq
    @40
    @78
    vx
    cB
    cD
    cR
    cS
    cE
    @70
    @6
    cI
    cV
    cW
    cX
    cZ
    cY
    prdsdsf.y
    prdsdsf.b
    @103
    @104
    @105
    @106
    wph
    @5
    @7
    @71
    @77
    simp22
    #
    prdsdsf.v
    prdsdsf.e
    prdsdsf.d
    prdsdsval3
    adantr
    breqtrrd
    #
    @91
    @75
    xrrege0
    syl22anc
    #
    readdcld
    #
    @88
    @42
    @43
    @44
    @63
    @93
    @95
    @97
    @66
    syl3anc
    @88
    @16
    @90
    @91
    cxad
    co
    #
    @92
    cle
    @88
    @42
    @102
    @43
    @44
    @16
    @139
    cle
    wbr
    @93
    @107
    @95
    @97
    @14
    @15
    @89
    cE
    cV
    xmettri2
    syl13anc
    @88
    @101
    @124
    @139
    @92
    wceq
    @121
    @137
    @90
    @91
    rexadd
    syl2anc
    breqtrd
    #
    @16
    @92
    xrrege0
    syl22anc
    @138
    @78
    @79
    cr
    wcel
    #
    @40
    @77
    wph
    @141
    @72
    @73
    @75
    readdcl
    3ad2ant3
    #
    adantr
    @140
    @88
    @90
    @91
    @73
    @75
    @121
    @137
    @110
    @127
    @120
    @136
    le2addd
    letrd
    ralrimiva
    @78
    @45
    vx
    cI
    wral
    @84
    @87
    wb
    @78
    @45
    vx
    cI
    @98
    ralrimiva
    @82
    @86
    vx
    vz
    cI
    @16
    @17
    cxr
    @53
    @23
    @16
    @79
    cle
    breq1
    ralrnmpt
    syl
    mpbird
    @78
    cc0
    @79
    cle
    wbr
    #
    @85
    @78
    @73
    @75
    @109
    @126
    @78
    @73
    @1
    wcel
    #
    cc0
    @73
    cle
    wbr
    #
    @78
    @70
    @4
    @1
    cB
    cB
    cD
    wph
    @72
    @2
    @77
    @3
    3ad2ant1
    #
    @106
    @119
    fovrnd
    @144
    @73
    cxr
    wcel
    @145
    @73
    elxrge0
    simprbi
    syl
    @78
    @75
    @1
    wcel
    #
    cc0
    @75
    cle
    wbr
    #
    @78
    @70
    @6
    @1
    cB
    cB
    cD
    @146
    @106
    @135
    fovrnd
    @147
    @75
    cxr
    wcel
    @148
    @75
    elxrge0
    simprbi
    syl
    addge0d
    @82
    @143
    vz
    cc0
    c0ex
    @23
    cc0
    @79
    cle
    breq1
    ralsn
    sylibr
    @82
    vz
    @18
    @19
    ralunb
    sylanbrc
    @78
    @38
    @79
    cxr
    wcel
    @81
    @83
    wb
    wph
    @72
    @38
    @77
    wph
    @5
    @7
    @38
    @71
    @54
    3adantr3
    3adant3
    @78
    @79
    @142
    rexrd
    vz
    @20
    @79
    supxrleub
    syl2anc
    mpbird
    eqbrtrd
    isxmet2d
end
