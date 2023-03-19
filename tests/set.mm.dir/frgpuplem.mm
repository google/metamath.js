include "wbr.mm"
include "wa.mm"
include "cpr.mm"
include "wss.mm"
include "ccom.mm"
include "cgsu.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "copab.mm"
include "wer.mm"
include "cop.mm"
include "c1o.mm"
include "cdif.mm"
include "cs2.mm"
include "cotp.mm"
include "csplice.mm"
include "c2o.mm"
include "wral.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "cab.mm"
include "cint.mm"
include "efgval.mm"
include "wcel.mm"
include "cxp.mm"
include "cin.mm"
include "cvv.mm"
include "coeq2.mm"
include "oveq2d.mm"
include "eqid.mm"
include "eqer.mm"
include "a1i.mm"
include "ssv.mm"
include "erinxp.mm"
include "wb.mm"
include "df-xp.mm"
include "ineq1i.mm"
include "incom.mm"
include "inopab.mm"
include "3eqtr3i.mm"
include "vex.mm"
include "prss.mm"
include "anbi1i.mm"
include "opabbii.mm"
include "eqtri.mm"
include "ereq1.mm"
include "ax-mp.mm"
include "sylib.mm"
include "simplrl.mm"
include "cword.mm"
include "cid.mm"
include "fviss.mm"
include "eqsstri.mm"
include "sseldi.mm"
include "opelxpi.mm"
include "adantl.mm"
include "simprl.mm"
include "2oconcl.mm"
include "ad2antll.mm"
include "syl2anc.mm"
include "s2cld.mm"
include "splcl.mm"
include "efgrcl.mm"
include "syl.mm"
include "simprd.mm"
include "eleqtrrd.mm"
include "jca.mm"
include "csubstr.mm"
include "cconcat.mm"
include "cplusg.mm"
include "wf.mm"
include "swrdcl.mm"
include "frgpuptf.mm"
include "ad2antrr.mm"
include "ccatco.mm"
include "syl3anc.mm"
include "cmnd.mm"
include "cgrp.mm"
include "grpmnd.mm"
include "wrdco.mm"
include "gsumccat.mm"
include "c0g.mm"
include "s2co.mm"
include "df-ov.mm"
include "cmpt2.mm"
include "efgmval.mm"
include "syl5eqr.mm"
include "fveq2d.mm"
include "frgpuptinv.mm"
include "sylan2.mm"
include "adantlr.mm"
include "eqtr3d.mm"
include "fveq2i.mm"
include "syl6reqr.mm"
include "s2eqd.mm"
include "eqtr4d.mm"
include "simprr.mm"
include "fovrnd.mm"
include "grpinvcl.mm"
include "gsumws2.mm"
include "grprinv.mm"
include "3eqtrd.mm"
include "gsumwcl.mm"
include "grprid.mm"
include "eqtrd.mm"
include "3eqtrrd.mm"
include "oveq1d.mm"
include "ccatcl.mm"
include "3eqtr4d.mm"
include "cuz.mm"
include "simplrr.mm"
include "elfzuz.mm"
include "eluzfz1.mm"
include "3syl.mm"
include "cn0.mm"
include "lencl.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "eluzfz2.mm"
include "ccatswrd.mm"
include "syl13anc.mm"
include "swrdid.mm"
include "coeq2d.mm"
include "splval.mm"
include "ovex.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "syl5bbr.mm"
include "eqeqan12d.mm"
include "anbi12d.mm"
include "braba.mm"
include "sylanbrc.mm"
include "ralrimivva.mm"
include "fvex.mm"
include "eqeltri.mm"
include "erex.mm"
include "mpisyl.mm"
include "breq.mm"
include "2ralbidv.mm"
include "elabg.mm"
include "mpbir2and.mm"
include "intss1.mm"
include "syl5eqss.mm"
include "ssbrd.mm"
include "imp.mm"
include "wrel.mm"
include "efger.mm"
include "errel.mm"
include "mp1i.mm"
include "brrelex12.mm"
include "sylan.mm"
include "preq12.mm"
include "sseq1d.mm"
include "brabga.mm"
include "mpbid.mm"

theorem frgpuplem
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let c.sm: class .~
  let cT: class T
  let cF: class F
  let cH: class H
  let cI: class I
  let cN: class N
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let vu: setvar u
  let vv: setvar v
  let vc: setvar c
  let vh: setvar h
  let vt: setvar t
  let cE: class E
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x
  let vi: setvar i
  let vj: setvar j
  let vw: setvar w
  let cK: class K
  let cM: class M
  let cG: class G
  let cX: class X
  assume frgpup.b: |- B = ( Base ` H )
  assume frgpup.n: |- N = ( invg ` H )
  assume frgpup.t: |- T = ( y e. I , z e. 2o |-> if ( z = (/) , ( F ` y ) , ( N ` ( F ` y ) ) ) )
  assume frgpup.h: |- ( ph -> H e. Grp )
  assume frgpup.i: |- ( ph -> I e. V )
  assume frgpup.a: |- ( ph -> F : I --> B )
  assume frgpup.w: |- W = ( _I ` Word ( I X. 2o ) )
  assume frgpup.r: |- .~ = ( ~FG ` I )

  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F y
  disjoint F z
  disjoint N y
  disjoint N z
  disjoint B y
  disjoint B z
  disjoint ph y
  disjoint ph z
  disjoint I y
  disjoint I z
  disjoint a b
  disjoint a g
  disjoint a u
  disjoint a v
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint b g
  disjoint b u
  disjoint b v
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint g u
  disjoint g v
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint u v
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint a c
  disjoint a h
  disjoint a t
  disjoint E a
  disjoint c h
  disjoint c t
  disjoint c u
  disjoint E c
  disjoint h t
  disjoint h u
  disjoint E h
  disjoint t u
  disjoint E t
  disjoint E u
  disjoint a n
  disjoint a r
  disjoint a x
  disjoint H a
  disjoint b c
  disjoint b h
  disjoint b n
  disjoint b r
  disjoint b t
  disjoint b x
  disjoint H b
  disjoint c g
  disjoint c n
  disjoint c r
  disjoint c v
  disjoint c x
  disjoint H c
  disjoint g h
  disjoint g n
  disjoint g r
  disjoint g t
  disjoint g x
  disjoint H g
  disjoint h n
  disjoint h r
  disjoint h v
  disjoint h x
  disjoint H h
  disjoint n r
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n x
  disjoint H n
  disjoint r t
  disjoint r u
  disjoint r v
  disjoint r x
  disjoint H r
  disjoint t v
  disjoint t x
  disjoint H t
  disjoint u x
  disjoint H u
  disjoint v x
  disjoint H v
  disjoint H x
  disjoint C u
  disjoint C v
  disjoint a i
  disjoint a j
  disjoint a w
  disjoint K a
  disjoint i j
  disjoint i n
  disjoint i t
  disjoint i w
  disjoint K i
  disjoint j n
  disjoint j t
  disjoint j w
  disjoint K j
  disjoint n w
  disjoint K n
  disjoint t w
  disjoint K t
  disjoint K w
  disjoint M a
  disjoint M b
  disjoint N a
  disjoint N b
  disjoint B a
  disjoint c y
  disjoint c z
  disjoint B c
  disjoint B g
  disjoint h y
  disjoint h z
  disjoint B h
  disjoint n y
  disjoint n z
  disjoint B n
  disjoint t y
  disjoint t z
  disjoint B t
  disjoint G a
  disjoint c w
  disjoint G c
  disjoint G t
  disjoint u w
  disjoint G u
  disjoint G w
  disjoint T a
  disjoint b i
  disjoint b j
  disjoint T b
  disjoint g i
  disjoint g j
  disjoint T g
  disjoint h i
  disjoint h j
  disjoint T h
  disjoint i r
  disjoint i u
  disjoint i v
  disjoint i x
  disjoint T i
  disjoint j r
  disjoint j u
  disjoint j v
  disjoint j x
  disjoint T j
  disjoint T n
  disjoint T r
  disjoint T u
  disjoint T v
  disjoint T x
  disjoint .~ a
  disjoint b w
  disjoint .~ b
  disjoint g w
  disjoint .~ g
  disjoint h w
  disjoint .~ h
  disjoint .~ i
  disjoint .~ j
  disjoint .~ n
  disjoint r w
  disjoint .~ r
  disjoint .~ t
  disjoint .~ u
  disjoint w x
  disjoint .~ w
  disjoint .~ x
  disjoint a ph
  disjoint b ph
  disjoint c i
  disjoint c j
  disjoint c ph
  disjoint g ph
  disjoint h ph
  disjoint i y
  disjoint i z
  disjoint i ph
  disjoint j y
  disjoint j z
  disjoint j ph
  disjoint n ph
  disjoint ph t
  disjoint ph u
  disjoint w y
  disjoint w z
  disjoint ph w
  disjoint x y
  disjoint x z
  disjoint ph x
  disjoint I a
  disjoint I b
  disjoint I i
  disjoint I j
  disjoint I n
  disjoint r y
  disjoint r z
  disjoint I r
  disjoint I w
  disjoint I x
  disjoint V w
  disjoint W a
  disjoint W b
  disjoint W g
  disjoint W h
  disjoint W n
  disjoint W r
  disjoint W t
  disjoint W u
  disjoint v w
  disjoint W v
  disjoint W w
  disjoint W x
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X n
  disjoint X u
  disjoint X w
  assert |- ( ( ph /\ A .~ C ) -> ( H gsum ( T o. A ) ) = ( H gsum ( T o. C ) ) )

  proof
    wph
    cA
    cC
    c.sm
    wbr
    #
    wa
    #
    cA
    cC
    cpr
    #
    cW
    wss
    #
    cH
    cT
    cA
    ccom
    #
    cgsu
    co
    #
    cH
    cT
    cC
    ccom
    #
    cgsu
    co
    #
    wceq
    #
    @1
    cA
    cC
    vu
    cv
    #
    vv
    cv
    #
    cpr
    #
    cW
    wss
    #
    cH
    cT
    @9
    ccom
    #
    cgsu
    co
    #
    cH
    cT
    @10
    ccom
    #
    cgsu
    co
    #
    wceq
    #
    wa
    #
    vu
    vv
    copab
    #
    wbr
    #
    @3
    @8
    wa
    #
    wph
    @0
    @20
    wph
    c.sm
    @19
    cA
    cC
    wph
    c.sm
    cW
    vr
    cv
    #
    wer
    #
    vx
    cv
    #
    @24
    vn
    cv
    #
    @25
    va
    cv
    #
    vb
    cv
    #
    cop
    #
    @26
    c1o
    @27
    cdif
    #
    cop
    #
    cs2
    #
    cotp
    #
    csplice
    co
    #
    @22
    wbr
    #
    vb
    c2o
    wral
    va
    cI
    wral
    #
    vn
    cc0
    @24
    chash
    cfv
    #
    cfz
    co
    #
    wral
    vx
    cW
    wral
    #
    wa
    #
    vr
    cab
    #
    cint
    #
    @19
    vx
    va
    vb
    c.sm
    vn
    cI
    cW
    vr
    frgpup.w
    frgpup.r
    efgval
    wph
    @19
    @40
    wcel
    #
    @41
    @19
    wss
    wph
    @42
    cW
    @19
    wer
    #
    @24
    @33
    @19
    wbr
    #
    vb
    c2o
    wral
    va
    cI
    wral
    #
    vn
    @37
    wral
    vx
    cW
    wral
    #
    wph
    cW
    @17
    vu
    vv
    copab
    #
    cW
    cW
    cxp
    #
    cin
    #
    wer
    #
    @43
    wph
    cvv
    cW
    @47
    cvv
    @47
    wer
    wph
    vu
    vv
    @14
    @16
    @47
    @9
    @10
    wceq
    @13
    @15
    cH
    cgsu
    @9
    @10
    cT
    coeq2
    oveq2d
    @47
    eqid
    eqer
    a1i
    cW
    cvv
    wss
    wph
    cW
    ssv
    a1i
    erinxp
    @49
    @19
    wceq
    @50
    @43
    wb
    @49
    @9
    cW
    wcel
    #
    @10
    cW
    wcel
    #
    wa
    #
    @17
    wa
    #
    vu
    vv
    copab
    #
    @19
    @48
    @47
    cin
    @53
    vu
    vv
    copab
    #
    @47
    cin
    @49
    @55
    @48
    @56
    @47
    vu
    vv
    cW
    cW
    df-xp
    ineq1i
    @48
    @47
    incom
    @53
    @17
    vu
    vv
    inopab
    3eqtr3i
    @54
    @18
    vu
    vv
    @53
    @12
    @17
    @9
    @10
    cW
    vu
    vex
    vv
    vex
    prss
    #
    anbi1i
    opabbii
    eqtri
    cW
    @49
    @19
    ereq1
    ax-mp
    sylib
    #
    wph
    @45
    vx
    vn
    cW
    @37
    wph
    @24
    cW
    wcel
    #
    @25
    @37
    wcel
    #
    wa
    #
    wa
    #
    @44
    va
    vb
    cI
    c2o
    @62
    @26
    cI
    wcel
    #
    @27
    c2o
    wcel
    #
    wa
    #
    wa
    #
    @59
    @33
    cW
    wcel
    #
    wa
    #
    cH
    cT
    @24
    ccom
    #
    cgsu
    co
    #
    cH
    cT
    @33
    ccom
    #
    cgsu
    co
    #
    wceq
    #
    @44
    @66
    @59
    @67
    wph
    @59
    @60
    @65
    simplrl
    #
    @66
    @33
    cI
    c2o
    cxp
    #
    cword
    #
    cW
    @66
    @24
    @76
    wcel
    #
    @31
    @76
    wcel
    #
    @33
    @76
    wcel
    @66
    cW
    @76
    @24
    cW
    @76
    cid
    cfv
    #
    @76
    frgpup.w
    @76
    fviss
    eqsstri
    @74
    sseldi
    #
    @66
    @28
    @30
    @75
    @65
    @28
    @75
    wcel
    #
    @62
    @26
    @27
    cI
    c2o
    opelxpi
    #
    adantl
    #
    @66
    @63
    @29
    c2o
    wcel
    #
    @30
    @75
    wcel
    @62
    @63
    @64
    simprl
    #
    @64
    @84
    @62
    @63
    @27
    2oconcl
    ad2antll
    @26
    @29
    cI
    c2o
    opelxpi
    syl2anc
    #
    s2cld
    #
    @75
    @31
    @24
    @25
    @25
    splcl
    syl2anc
    @66
    cI
    cvv
    wcel
    #
    cW
    @76
    wceq
    #
    @66
    @59
    @88
    @89
    wa
    @74
    @24
    cI
    cW
    frgpup.w
    efgrcl
    syl
    simprd
    eleqtrrd
    jca
    @66
    cH
    cT
    @24
    cc0
    @25
    cop
    csubstr
    co
    #
    ccom
    #
    cT
    @24
    @25
    @36
    cop
    csubstr
    co
    #
    ccom
    #
    cconcat
    co
    #
    cgsu
    co
    #
    cH
    cT
    @90
    @31
    cconcat
    co
    #
    ccom
    #
    @93
    cconcat
    co
    #
    cgsu
    co
    #
    @70
    @72
    @66
    cH
    @91
    cgsu
    co
    #
    cH
    @93
    cgsu
    co
    #
    cH
    cplusg
    cfv
    #
    co
    #
    cH
    @97
    cgsu
    co
    #
    @101
    @102
    co
    #
    @95
    @99
    @66
    @100
    @104
    @101
    @102
    @66
    @104
    cH
    @91
    cT
    @31
    ccom
    #
    cconcat
    co
    #
    cgsu
    co
    #
    @100
    cH
    @106
    cgsu
    co
    #
    @102
    co
    #
    @100
    @66
    @97
    @107
    cH
    cgsu
    @66
    @90
    @76
    wcel
    #
    @78
    @75
    cB
    cT
    wf
    #
    @97
    @107
    wceq
    @66
    @77
    @111
    @80
    @75
    @24
    cc0
    @25
    swrdcl
    syl
    #
    @87
    wph
    @112
    @61
    @65
    wph
    vy
    vz
    cB
    cT
    cF
    cH
    cI
    cN
    cV
    frgpup.b
    frgpup.n
    frgpup.t
    frgpup.h
    frgpup.i
    frgpup.a
    frgpuptf
    ad2antrr
    #
    @75
    cB
    @90
    @31
    cT
    ccatco
    syl3anc
    oveq2d
    @66
    cH
    cmnd
    wcel
    #
    @91
    cB
    cword
    #
    wcel
    #
    @106
    @116
    wcel
    #
    @108
    @110
    wceq
    @66
    cH
    cgrp
    wcel
    #
    @115
    wph
    @119
    @61
    @65
    frgpup.h
    ad2antrr
    #
    cH
    grpmnd
    syl
    #
    @66
    @111
    @112
    @117
    @113
    @114
    @75
    cB
    cT
    @90
    wrdco
    syl2anc
    #
    @66
    @78
    @112
    @118
    @87
    @114
    @75
    cB
    cT
    @31
    wrdco
    syl2anc
    cB
    @102
    cH
    @91
    @106
    frgpup.b
    @102
    eqid
    #
    gsumccat
    syl3anc
    @66
    @110
    @100
    cH
    c0g
    cfv
    #
    @102
    co
    #
    @100
    @66
    @109
    @124
    @100
    @102
    @66
    @109
    cH
    @26
    @27
    cT
    co
    #
    @126
    cN
    cfv
    #
    cs2
    #
    cgsu
    co
    #
    @126
    @127
    @102
    co
    #
    @124
    @66
    @106
    @128
    cH
    cgsu
    @66
    @106
    @28
    cT
    cfv
    #
    @30
    cT
    cfv
    #
    cs2
    @128
    @66
    @28
    @30
    cT
    @75
    cB
    @114
    @83
    @86
    s2co
    @66
    @126
    @127
    @131
    @132
    @126
    @131
    wceq
    @66
    @26
    @27
    cT
    df-ov
    #
    a1i
    @66
    @132
    @131
    cN
    cfv
    #
    @127
    @66
    @28
    vy
    vz
    cI
    c2o
    vy
    cv
    c1o
    vz
    cv
    cdif
    cop
    cmpt2
    #
    cfv
    #
    cT
    cfv
    #
    @132
    @134
    @66
    @136
    @30
    cT
    @65
    @136
    @30
    wceq
    @62
    @65
    @136
    @26
    @27
    @135
    co
    @30
    @26
    @27
    @135
    df-ov
    vy
    vz
    @26
    @27
    cI
    @135
    @135
    eqid
    #
    efgmval
    syl5eqr
    adantl
    fveq2d
    wph
    @65
    @137
    @134
    wceq
    #
    @61
    @65
    wph
    @81
    @139
    @82
    wph
    vy
    vz
    @28
    cB
    cT
    cF
    cH
    cI
    @135
    cN
    cV
    frgpup.b
    frgpup.n
    frgpup.t
    frgpup.h
    frgpup.i
    frgpup.a
    @138
    frgpuptinv
    sylan2
    adantlr
    eqtr3d
    @126
    @131
    cN
    @133
    fveq2i
    syl6reqr
    s2eqd
    eqtr4d
    oveq2d
    @66
    @115
    @126
    cB
    wcel
    #
    @127
    cB
    wcel
    #
    @129
    @130
    wceq
    @121
    @66
    @26
    @27
    cB
    cI
    c2o
    cT
    @114
    @85
    @62
    @63
    @64
    simprr
    fovrnd
    #
    @66
    @119
    @140
    @141
    @120
    @142
    cB
    cH
    cN
    @126
    frgpup.b
    frgpup.n
    grpinvcl
    syl2anc
    cB
    @102
    @126
    @127
    cH
    frgpup.b
    @123
    gsumws2
    syl3anc
    @66
    @119
    @140
    @130
    @124
    wceq
    @120
    @142
    cB
    @102
    cH
    cN
    @126
    @124
    frgpup.b
    @123
    @124
    eqid
    #
    frgpup.n
    grprinv
    syl2anc
    3eqtrd
    oveq2d
    @66
    @119
    @100
    cB
    wcel
    #
    @125
    @100
    wceq
    @120
    @66
    @115
    @117
    @144
    @121
    @122
    cB
    cH
    @91
    frgpup.b
    gsumwcl
    syl2anc
    cB
    @102
    cH
    @100
    @124
    frgpup.b
    @123
    @143
    grprid
    syl2anc
    eqtrd
    3eqtrrd
    oveq1d
    @66
    @115
    @117
    @93
    @116
    wcel
    #
    @95
    @103
    wceq
    @121
    @122
    @66
    @92
    @76
    wcel
    #
    @112
    @145
    @66
    @77
    @146
    @80
    @75
    @24
    @25
    @36
    swrdcl
    syl
    #
    @114
    @75
    cB
    cT
    @92
    wrdco
    syl2anc
    #
    cB
    @102
    cH
    @91
    @93
    frgpup.b
    @123
    gsumccat
    syl3anc
    @66
    @115
    @97
    @116
    wcel
    #
    @145
    @99
    @105
    wceq
    @121
    @66
    @96
    @76
    wcel
    #
    @112
    @149
    @66
    @111
    @78
    @150
    @113
    @87
    @75
    @90
    @31
    ccatcl
    syl2anc
    #
    @114
    @75
    cB
    cT
    @96
    wrdco
    syl2anc
    @148
    cB
    @102
    cH
    @97
    @93
    frgpup.b
    @123
    gsumccat
    syl3anc
    3eqtr4d
    @66
    @69
    @94
    cH
    cgsu
    @66
    cT
    @90
    @92
    cconcat
    co
    #
    ccom
    #
    @69
    @94
    @66
    @152
    @24
    cT
    @66
    @152
    @24
    cc0
    @36
    cop
    csubstr
    co
    #
    @24
    @66
    @77
    cc0
    cc0
    @25
    cfz
    co
    wcel
    #
    @60
    @36
    @37
    wcel
    #
    @152
    @154
    wceq
    @80
    @66
    @60
    @25
    cc0
    cuz
    cfv
    #
    wcel
    @155
    wph
    @59
    @60
    @65
    simplrr
    #
    @25
    cc0
    @36
    elfzuz
    cc0
    @25
    eluzfz1
    3syl
    @158
    @66
    @36
    @157
    wcel
    @156
    @66
    @36
    cn0
    @157
    @66
    @77
    @36
    cn0
    wcel
    @80
    @75
    @24
    lencl
    syl
    nn0uz
    syl6eleq
    cc0
    @36
    eluzfz2
    syl
    @75
    @24
    cc0
    @25
    @36
    ccatswrd
    syl13anc
    @66
    @77
    @154
    @24
    wceq
    @80
    @75
    @24
    swrdid
    syl
    eqtrd
    coeq2d
    @66
    @111
    @146
    @112
    @153
    @94
    wceq
    @113
    @147
    @114
    @75
    cB
    @90
    @92
    cT
    ccatco
    syl3anc
    eqtr3d
    oveq2d
    @66
    @71
    @98
    cH
    cgsu
    @66
    @71
    cT
    @96
    @92
    cconcat
    co
    #
    ccom
    #
    @98
    @66
    @33
    @159
    cT
    @66
    @59
    @60
    @60
    @78
    @33
    @159
    wceq
    @74
    @158
    @158
    @87
    @31
    @24
    @25
    @25
    cW
    @37
    @37
    @76
    splval
    syl13anc
    coeq2d
    @66
    @150
    @146
    @112
    @160
    @98
    wceq
    @151
    @147
    @114
    @75
    cB
    @96
    @92
    cT
    ccatco
    syl3anc
    eqtrd
    oveq2d
    3eqtr4d
    @18
    @68
    @73
    wa
    vu
    vv
    @24
    @33
    @19
    vx
    vex
    @24
    @32
    csplice
    ovex
    @9
    @24
    wceq
    #
    @10
    @33
    wceq
    #
    wa
    #
    @12
    @68
    @17
    @73
    @12
    @53
    @163
    @68
    @57
    @161
    @51
    @59
    @162
    @52
    @67
    @9
    @24
    cW
    eleq1
    @10
    @33
    cW
    eleq1
    bi2anan9
    syl5bbr
    @161
    @162
    @14
    @70
    @16
    @72
    @161
    @13
    @69
    cH
    cgsu
    @9
    @24
    cT
    coeq2
    oveq2d
    @162
    @15
    @71
    cH
    cgsu
    @10
    @33
    cT
    coeq2
    oveq2d
    eqeqan12d
    anbi12d
    @19
    eqid
    #
    braba
    sylanbrc
    ralrimivva
    ralrimivva
    wph
    @19
    cvv
    wcel
    #
    @42
    @43
    @46
    wa
    #
    wb
    wph
    @43
    cW
    cvv
    wcel
    @165
    @58
    cW
    @79
    cvv
    frgpup.w
    @76
    cid
    fvex
    eqeltri
    cW
    @19
    cvv
    erex
    mpisyl
    @39
    @166
    vr
    @19
    cvv
    @22
    @19
    wceq
    #
    @23
    @43
    @38
    @46
    cW
    @22
    @19
    ereq1
    @167
    @35
    @45
    vx
    vn
    cW
    @37
    @167
    @34
    @44
    va
    vb
    cI
    c2o
    @24
    @33
    @22
    @19
    breq
    2ralbidv
    2ralbidv
    anbi12d
    elabg
    syl
    mpbir2and
    @19
    @40
    intss1
    syl
    syl5eqss
    ssbrd
    imp
    @1
    cA
    cvv
    wcel
    cC
    cvv
    wcel
    wa
    #
    @20
    @21
    wb
    wph
    c.sm
    wrel
    #
    @0
    @168
    cW
    c.sm
    wer
    @169
    wph
    c.sm
    cI
    cW
    frgpup.w
    frgpup.r
    efger
    cW
    c.sm
    errel
    mp1i
    cA
    cC
    c.sm
    brrelex12
    sylan
    @18
    @21
    vu
    vv
    cA
    cC
    @19
    cvv
    cvv
    @9
    cA
    wceq
    #
    @10
    cC
    wceq
    #
    wa
    #
    @12
    @3
    @17
    @8
    @172
    @11
    @2
    cW
    @9
    @10
    cA
    cC
    preq12
    sseq1d
    @170
    @171
    @14
    @5
    @16
    @7
    @170
    @13
    @4
    cH
    cgsu
    @9
    cA
    cT
    coeq2
    oveq2d
    @171
    @15
    @6
    cH
    cgsu
    @10
    cC
    cT
    coeq2
    oveq2d
    eqeqan12d
    anbi12d
    @164
    brabga
    syl
    mpbid
    simprd
end
