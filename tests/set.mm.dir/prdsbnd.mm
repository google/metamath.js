include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "cxp.mm"
include "cc0.mm"
include "cv.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "cr.mm"
include "wrex.mm"
include "cbnd.mm"
include "cmpt.mm"
include "cprds.mm"
include "cds.mm"
include "cbs.mm"
include "cvv.mm"
include "eqid.mm"
include "wa.mm"
include "fvexd.mm"
include "bndmet.mm"
include "syl.mm"
include "prdsmet.mm"
include "wfn.mm"
include "wceq.mm"
include "dffn5.mm"
include "sylib.mm"
include "oveq2d.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "3eltr4d.mm"
include "wral.mm"
include "cfn.mm"
include "wex.mm"
include "isbnd3.mm"
include "simprbi.mm"
include "ralrimiva.mm"
include "oveq2.mm"
include "feq3d.mm"
include "ac6sfi.mm"
include "syl2anc.mm"
include "crn.mm"
include "csn.mm"
include "cun.mm"
include "clt.mm"
include "csup.mm"
include "wss.mm"
include "frn.mm"
include "adantl.mm"
include "0red.mm"
include "snssd.mm"
include "adantr.mm"
include "unssd.mm"
include "c0.mm"
include "wne.mm"
include "wfo.mm"
include "ffn.mm"
include "dffn4.mm"
include "fofi.mm"
include "syl2an.mm"
include "snfi.mm"
include "unfi.mm"
include "sylancl.mm"
include "ssun2.mm"
include "c0ex.mm"
include "snid.mm"
include "sselii.mm"
include "ne0i.mm"
include "mp1i.mm"
include "wor.mm"
include "w3a.mm"
include "ltso.mm"
include "fisupcl.mm"
include "mpan.mm"
include "syl3anc.mm"
include "sseldd.mm"
include "adantrr.mm"
include "metf.mm"
include "3syl.mm"
include "cle.mm"
include "wbr.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "simprr.mm"
include "metcl.mm"
include "metge0.mm"
include "cxr.mm"
include "oveqdr.mm"
include "eleqtrd.mm"
include "prdsdsval3.mm"
include "eqtrd.mm"
include "adantlr.mm"
include "prdsbascl.mm"
include "r19.21bi.mm"
include "ad2ant2r.mm"
include "ffvelrn.mm"
include "ad2ant2lr.mm"
include "fovrnd.mm"
include "wb.mm"
include "0re.mm"
include "elicc2.mm"
include "sylancr.mm"
include "mpbid.mm"
include "simp3d.mm"
include "fimaxre2.mm"
include "ssun1.mm"
include "ad2antlr.mm"
include "fnfvelrn.mm"
include "sseldi.mm"
include "suprub.mm"
include "syl31anc.mm"
include "letrd.mm"
include "expr.mm"
include "ralimdva.mm"
include "impr.mm"
include "ovex.mm"
include "rgenw.mm"
include "breq1.mm"
include "ralrnmpt.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "a1i.mm"
include "elsni.mm"
include "breq1d.mm"
include "syl5ibrcom.mm"
include "ralrimiv.mm"
include "ralunb.mm"
include "sylanbrc.mm"
include "fmptd.mm"
include "ressxr.mm"
include "syl6ss.mm"
include "rexrd.mm"
include "supxrleub.mm"
include "mpbird.mm"
include "eqbrtrd.mm"
include "mpbir3and.mm"
include "an32s.mm"
include "ralrimivva.mm"
include "ffnov.mm"
include "rspcev.mm"
include "exlimddv.mm"

theorem prdsbnd
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
  assume prdsbnd.m: |- ( ( ph /\ x e. I ) -> E e. ( Bnd ` V ) )

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
  assert |- ( ph -> D e. ( Bnd ` B ) )

  proof
    wph
    cD
    cB
    cme
    cfv
    #
    wcel
    #
    cB
    cB
    cxp
    #
    cc0
    vm
    cv
    #
    cicc
    co
    #
    cD
    wf
    #
    vm
    cr
    wrex
    #
    cD
    cB
    cbnd
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
    @10
    cbs
    cfv
    #
    cme
    cfv
    cD
    @0
    wph
    vx
    @12
    @11
    @8
    cS
    cE
    cI
    cV
    cW
    @10
    cvv
    @10
    eqid
    #
    @12
    eqid
    #
    prdsbnd.v
    prdsbnd.e
    @11
    eqid
    #
    prdsbnd.s
    prdsbnd.i
    wph
    @7
    cI
    wcel
    #
    wa
    #
    @7
    cR
    fvexd
    @17
    cE
    cV
    cbnd
    cfv
    wcel
    #
    cE
    cV
    cme
    cfv
    wcel
    #
    prdsbnd.m
    cE
    cV
    bndmet
    syl
    #
    prdsmet
    wph
    cD
    cY
    cds
    cfv
    @11
    prdsbnd.d
    wph
    cY
    @10
    cds
    wph
    cY
    cS
    cR
    cprds
    co
    @10
    prdsbnd.y
    wph
    cR
    @9
    cS
    cprds
    wph
    cR
    cI
    wfn
    cR
    @9
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
    #
    wph
    cB
    @12
    cme
    wph
    cB
    cY
    cbs
    cfv
    @12
    prdsbnd.b
    wph
    cY
    @10
    cbs
    @21
    fveq2d
    syl5eq
    #
    fveq2d
    3eltr4d
    #
    wph
    cI
    cr
    vk
    cv
    #
    wf
    #
    cV
    cV
    cxp
    #
    cc0
    @7
    @25
    cfv
    #
    cicc
    co
    #
    cE
    wf
    #
    vx
    cI
    wral
    #
    wa
    #
    @6
    vk
    wph
    cI
    cfn
    wcel
    #
    @27
    cc0
    vw
    cv
    #
    cicc
    co
    #
    cE
    wf
    #
    vw
    cr
    wrex
    #
    vx
    cI
    wral
    @32
    vk
    wex
    prdsbnd.i
    wph
    @37
    vx
    cI
    @17
    @18
    @37
    prdsbnd.m
    @18
    @19
    @37
    vw
    cE
    cV
    isbnd3
    simprbi
    syl
    ralrimiva
    @36
    @30
    vx
    vw
    cI
    cr
    vk
    @34
    @28
    wceq
    @35
    @29
    cE
    @27
    @34
    @28
    cc0
    cicc
    oveq2
    feq3d
    ac6sfi
    syl2anc
    wph
    @32
    wa
    #
    @25
    crn
    #
    cc0
    csn
    #
    cun
    #
    cr
    clt
    csup
    #
    cr
    wcel
    #
    @2
    cc0
    @42
    cicc
    co
    #
    cD
    wf
    #
    @6
    wph
    @26
    @43
    @31
    wph
    @26
    wa
    #
    @41
    cr
    @42
    @46
    @39
    @40
    cr
    @26
    @39
    cr
    wss
    wph
    cI
    cr
    @25
    frn
    adantl
    wph
    @40
    cr
    wss
    @26
    wph
    cc0
    cr
    wph
    0red
    snssd
    adantr
    unssd
    #
    @46
    @41
    cfn
    wcel
    #
    @41
    c0
    wne
    #
    @41
    cr
    wss
    #
    @42
    @41
    wcel
    #
    @46
    @39
    cfn
    wcel
    #
    @40
    cfn
    wcel
    @48
    wph
    @33
    cI
    @39
    @25
    wfo
    #
    @52
    @26
    prdsbnd.i
    @26
    @25
    cI
    wfn
    #
    @53
    cI
    cr
    @25
    ffn
    #
    cI
    @25
    dffn4
    sylib
    cI
    @39
    @25
    fofi
    syl2an
    cc0
    snfi
    @39
    @40
    unfi
    sylancl
    #
    cc0
    @41
    wcel
    #
    @49
    @46
    @40
    @41
    cc0
    @40
    @39
    ssun2
    cc0
    c0ex
    snid
    sselii
    #
    @41
    cc0
    ne0i
    #
    mp1i
    @47
    cr
    clt
    wor
    @48
    @49
    @50
    w3a
    @51
    ltso
    cr
    @41
    clt
    fisupcl
    mpan
    syl3anc
    sseldd
    #
    adantrr
    #
    @38
    cD
    @2
    wfn
    #
    vf
    cv
    #
    vg
    cv
    #
    cD
    co
    #
    @44
    wcel
    #
    vg
    cB
    wral
    vf
    cB
    wral
    @45
    wph
    @62
    @32
    wph
    @1
    @2
    cr
    cD
    wf
    @62
    @24
    cD
    cB
    metf
    @2
    cr
    cD
    ffn
    3syl
    adantr
    @38
    @66
    vf
    vg
    cB
    cB
    wph
    @63
    cB
    wcel
    #
    @64
    cB
    wcel
    #
    wa
    #
    @32
    @66
    wph
    @69
    wa
    #
    @32
    wa
    #
    @66
    @65
    cr
    wcel
    #
    cc0
    @65
    cle
    wbr
    #
    @65
    @42
    cle
    wbr
    #
    @71
    @1
    @67
    @68
    @72
    wph
    @1
    @69
    @32
    @24
    ad2antrr
    #
    @70
    @67
    @32
    wph
    @67
    @68
    simprl
    #
    adantr
    #
    @70
    @68
    @32
    wph
    @67
    @68
    simprr
    #
    adantr
    #
    @63
    @64
    cD
    cB
    metcl
    syl3anc
    @71
    @1
    @67
    @68
    @73
    @75
    @77
    @79
    @63
    @64
    cD
    cB
    metge0
    syl3anc
    @71
    @65
    vx
    cI
    @7
    @63
    cfv
    #
    @7
    @64
    cfv
    #
    cE
    co
    #
    cmpt
    #
    crn
    #
    @40
    cun
    #
    cxr
    clt
    csup
    #
    @42
    cle
    @70
    @65
    @86
    wceq
    @32
    @70
    @65
    @63
    @64
    @11
    co
    @86
    wph
    @69
    vf
    vg
    cD
    @11
    @22
    oveqdr
    @70
    vx
    @12
    @11
    @8
    cS
    cE
    @63
    @64
    cI
    cV
    cW
    cfn
    cvv
    @10
    @13
    @14
    wph
    cS
    cW
    wcel
    @69
    prdsbnd.s
    adantr
    #
    wph
    @33
    @69
    prdsbnd.i
    adantr
    #
    @70
    @8
    cvv
    wcel
    vx
    cI
    @70
    @16
    wa
    #
    @7
    cR
    fvexd
    ralrimiva
    #
    @70
    @63
    cB
    @12
    @76
    wph
    cB
    @12
    wceq
    @69
    @23
    adantr
    #
    eleqtrd
    #
    @70
    @64
    cB
    @12
    @78
    @91
    eleqtrd
    #
    prdsbnd.v
    prdsbnd.e
    @15
    prdsdsval3
    eqtrd
    adantr
    @71
    @86
    @42
    cle
    wbr
    #
    @34
    @42
    cle
    wbr
    #
    vw
    @85
    wral
    #
    @71
    @95
    vw
    @84
    wral
    #
    @95
    vw
    @40
    wral
    @96
    @71
    @82
    @42
    cle
    wbr
    #
    vx
    cI
    wral
    #
    @97
    @70
    @26
    @31
    @99
    @70
    @26
    wa
    #
    @30
    @98
    vx
    cI
    @100
    @16
    @30
    @98
    @100
    @16
    @30
    wa
    #
    wa
    #
    @82
    @28
    @42
    @70
    @16
    @82
    cr
    wcel
    #
    @26
    @30
    @89
    @19
    @80
    cV
    wcel
    #
    @81
    cV
    wcel
    #
    @103
    wph
    @16
    @19
    @69
    @20
    adantlr
    @70
    @104
    vx
    cI
    @70
    vx
    @12
    @8
    cS
    @63
    cI
    cV
    cW
    cfn
    cvv
    @10
    @13
    @14
    @87
    @88
    @90
    prdsbnd.v
    @92
    prdsbascl
    r19.21bi
    #
    @70
    @105
    vx
    cI
    @70
    vx
    @12
    @8
    cS
    @64
    cI
    cV
    cW
    cfn
    cvv
    @10
    @13
    @14
    @87
    @88
    @90
    prdsbnd.v
    @93
    prdsbascl
    r19.21bi
    #
    @80
    @81
    cE
    cV
    metcl
    syl3anc
    #
    ad2ant2r
    @26
    @16
    @28
    cr
    wcel
    #
    @70
    @30
    cI
    cr
    @7
    @25
    ffvelrn
    ad2ant2lr
    #
    @100
    @43
    @101
    wph
    @26
    @43
    @69
    @60
    adantlr
    adantr
    @102
    @103
    cc0
    @82
    cle
    wbr
    #
    @82
    @28
    cle
    wbr
    #
    @102
    @82
    @29
    wcel
    #
    @103
    @111
    @112
    w3a
    #
    @102
    @80
    @81
    @29
    cV
    cV
    cE
    @100
    @16
    @30
    simprr
    @70
    @16
    @104
    @26
    @30
    @106
    ad2ant2r
    @70
    @16
    @105
    @26
    @30
    @107
    ad2ant2r
    fovrnd
    @102
    cc0
    cr
    wcel
    #
    @109
    @113
    @114
    wb
    0re
    @110
    cc0
    @28
    @82
    elicc2
    sylancr
    mpbid
    simp3d
    @102
    @50
    @49
    @34
    vz
    cv
    cle
    wbr
    vw
    @41
    wral
    vz
    cr
    wrex
    #
    @28
    @41
    wcel
    @28
    @42
    cle
    wbr
    @100
    @50
    @101
    wph
    @26
    @50
    @69
    @47
    adantlr
    adantr
    @57
    @49
    @102
    @58
    @59
    mp1i
    @100
    @116
    @101
    wph
    @26
    @116
    @69
    @46
    @50
    @48
    @116
    @47
    @56
    vz
    vw
    @41
    fimaxre2
    syl2anc
    #
    adantlr
    adantr
    @102
    @39
    @41
    @28
    @39
    @40
    ssun1
    @102
    @54
    @16
    @28
    @39
    wcel
    @26
    @54
    @70
    @101
    @55
    ad2antlr
    @100
    @16
    @30
    simprl
    cI
    @7
    @25
    fnfvelrn
    syl2anc
    sseldi
    vz
    vw
    @41
    @28
    suprub
    syl31anc
    letrd
    expr
    ralimdva
    impr
    @82
    cvv
    wcel
    #
    vx
    cI
    wral
    @97
    @99
    wb
    @118
    vx
    cI
    @80
    @81
    cE
    ovex
    rgenw
    @95
    @98
    vx
    vw
    cI
    @82
    @83
    cvv
    @83
    eqid
    #
    @34
    @82
    @42
    cle
    breq1
    ralrnmpt
    ax-mp
    sylibr
    @71
    @95
    vw
    @40
    @71
    @95
    @34
    @40
    wcel
    #
    cc0
    @42
    cle
    wbr
    #
    @71
    @50
    @49
    @116
    @57
    @121
    wph
    @26
    @50
    @69
    @31
    @47
    ad2ant2r
    @57
    @49
    @71
    @58
    @59
    mp1i
    wph
    @26
    @116
    @69
    @31
    @117
    ad2ant2r
    @57
    @71
    @58
    a1i
    vz
    vw
    @41
    cc0
    suprub
    syl31anc
    @120
    @34
    cc0
    @42
    cle
    @34
    cc0
    elsni
    breq1d
    syl5ibrcom
    ralrimiv
    @95
    vw
    @84
    @40
    ralunb
    sylanbrc
    @71
    @85
    cxr
    wss
    #
    @42
    cxr
    wcel
    @94
    @96
    wb
    @70
    @122
    @32
    @70
    @85
    cr
    cxr
    @70
    @84
    @40
    cr
    @70
    cI
    cr
    @83
    wf
    @84
    cr
    wss
    @70
    vx
    cI
    @82
    cr
    @83
    @108
    @119
    fmptd
    cI
    cr
    @83
    frn
    syl
    @70
    cc0
    cr
    @70
    0red
    snssd
    unssd
    ressxr
    syl6ss
    adantr
    @71
    @42
    wph
    @32
    @43
    @69
    @61
    adantlr
    #
    rexrd
    vw
    @85
    @42
    supxrleub
    syl2anc
    mpbird
    eqbrtrd
    @71
    @115
    @43
    @66
    @72
    @73
    @74
    w3a
    wb
    0re
    @123
    cc0
    @42
    @65
    elicc2
    sylancr
    mpbir3and
    an32s
    ralrimivva
    vf
    vg
    cB
    cB
    @44
    cD
    ffnov
    sylanbrc
    @5
    @45
    vm
    @42
    cr
    @3
    @42
    wceq
    @4
    @44
    cD
    @2
    @3
    @42
    cc0
    cicc
    oveq2
    feq3d
    rspcev
    syl2anc
    exlimddv
    vm
    cD
    cB
    isbnd3
    sylanbrc
end
