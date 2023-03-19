include "cplusg.mm"
include "cfv.mm"
include "cvsca.mm"
include "cbs.mm"
include "wceq.mm"
include "a1i.mm"
include "eqidd.mm"
include "cip.mm"
include "c0g.mm"
include "cdr.mm"
include "wcel.mm"
include "csca.mm"
include "ccrg.mm"
include "cfield.mm"
include "wa.mm"
include "isfld.mm"
include "sylib.mm"
include "simpld.mm"
include "frlmsca.mm"
include "syl2anc.mm"
include "cmulr.mm"
include "cstv.mm"
include "clmod.mm"
include "clvec.mm"
include "crg.mm"
include "drngring.mm"
include "syl.mm"
include "frlmlmod.mm"
include "eqeltrrd.mm"
include "eqid.mm"
include "islvec.mm"
include "sylanbrc.mm"
include "simprd.mm"
include "idsrngd.mm"
include "cv.mm"
include "w3a.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cof.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3.mm"
include "frlmipval.mm"
include "syl22anc.mm"
include "wf.mm"
include "wfn.mm"
include "cmap.mm"
include "frlmbasmap.mm"
include "elmapi.mm"
include "ffn.mm"
include "inidm.mm"
include "offval.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "ccmn.mm"
include "ringcmn.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "fmptd.mm"
include "frlmphllem.mm"
include "gsumcl.mm"
include "eqeltrd.mm"
include "simp31.mm"
include "simp33.mm"
include "simp32.mm"
include "cfsupp.mm"
include "weq.mm"
include "fveq2.mm"
include "cbvmptv.mm"
include "oveq1i.mm"
include "fneq1i.mm"
include "cvv.mm"
include "simpr.mm"
include "fveq2d.mm"
include "ovexd.mm"
include "fvmptd.mm"
include "ringass.mm"
include "syl13anc.mm"
include "mpteq2dva.mm"
include "syl5eq.mm"
include "wfun.mm"
include "wbr.mm"
include "csupp.mm"
include "wss.mm"
include "funmpt.mm"
include "funeqd.mm"
include "mpbiri.mm"
include "anim12i.mm"
include "3adant2.mm"
include "frlmbasfsupp.mm"
include "ring0cl.mm"
include "ringrz.mm"
include "sylan.mm"
include "suppofss2d.mm"
include "fsuppsssupp.mm"
include "eqbrtrrd.mm"
include "simp1.mm"
include "wi.mm"
include "eleq1.mm"
include "id.mm"
include "oveq12d.mm"
include "eqeq1d.mm"
include "3anbi23d.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "chvarv.mm"
include "gsummptfsadd.mm"
include "cmpt2.mm"
include "frlmip.mm"
include "syl6reqr.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "mpteq2dv.mm"
include "cbvmpt2v.mm"
include "syl6eqr.mm"
include "simprl.mm"
include "fveq1d.mm"
include "simprr.mm"
include "eleqtrd.mm"
include "lmodvscl.mm"
include "lmodvacl.mm"
include "ovmpt2d.mm"
include "frlmplusgval.mm"
include "3syl.mm"
include "frlmvscaval.mm"
include "fvmpt2d.mm"
include "ringdir.mm"
include "3eqtrd.mm"
include "gsummulc2.mm"
include "eqtr4d.mm"
include "3eqtr4d.mm"
include "crngcom.mm"
include "wral.mm"
include "ralrimiva.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "3eqtr4rd.mm"
include "isphld.mm"

theorem frlmphl
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let vg: setvar g
  let c.xi: class .,
  let cI: class I
  let c.as: class .*
  let cO: class O
  let cV: class V
  let cW: class W
  let cY: class Y
  let c.0: class .0.
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cX: class X
  let ve: setvar e
  let vh: setvar h
  let vi: setvar i
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  assume frlmphl.y: |- Y = ( R freeLMod I )
  assume frlmphl.b: |- B = ( Base ` R )
  assume frlmphl.t: |- .x. = ( .r ` R )
  assume frlmphl.v: |- V = ( Base ` Y )
  assume frlmphl.j: |- ., = ( .i ` Y )
  assume frlmphl.o: |- O = ( 0g ` Y )
  assume frlmphl.0: |- .0. = ( 0g ` R )
  assume frlmphl.s: |- .* = ( *r ` R )
  assume frlmphl.f: |- ( ph -> R e. Field )
  assume frlmphl.m: |- ( ( ph /\ g e. V /\ ( g ., g ) = .0. ) -> g = O )
  assume frlmphl.u: |- ( ( ph /\ x e. B ) -> ( .* ` x ) = x )
  assume frlmphl.i: |- ( ph -> I e. W )

  disjoint B g
  disjoint B x
  disjoint g x
  disjoint I g
  disjoint I x
  disjoint R g
  disjoint R x
  disjoint V g
  disjoint V x
  disjoint W g
  disjoint W x
  disjoint .x. g
  disjoint .x. x
  disjoint Y g
  disjoint Y x
  disjoint .0. g
  disjoint .0. x
  disjoint g ph
  disjoint ph x
  disjoint ., g
  disjoint ., x
  disjoint O g
  disjoint .* x
  disjoint B f
  disjoint f g
  disjoint f x
  disjoint I f
  disjoint R f
  disjoint V f
  disjoint W f
  disjoint F f
  disjoint F g
  disjoint F x
  disjoint G f
  disjoint G g
  disjoint G x
  disjoint X f
  disjoint X g
  disjoint X x
  disjoint .x. f
  disjoint B e
  disjoint B h
  disjoint B i
  disjoint B y
  disjoint B z
  disjoint e f
  disjoint e g
  disjoint e h
  disjoint e i
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint f h
  disjoint f i
  disjoint f y
  disjoint f z
  disjoint g h
  disjoint g i
  disjoint g y
  disjoint g z
  disjoint h i
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint I e
  disjoint I h
  disjoint I i
  disjoint I y
  disjoint I z
  disjoint R e
  disjoint R h
  disjoint R i
  disjoint V e
  disjoint V h
  disjoint V i
  disjoint V y
  disjoint V z
  disjoint W h
  disjoint W i
  disjoint Y e
  disjoint Y f
  disjoint Y h
  disjoint Y i
  disjoint Y k
  disjoint e k
  disjoint f k
  disjoint g k
  disjoint h k
  disjoint i k
  disjoint k x
  disjoint .0. f
  disjoint .0. h
  disjoint .0. i
  disjoint .0. y
  disjoint e ph
  disjoint f ph
  disjoint h ph
  disjoint i ph
  disjoint k y
  disjoint k z
  disjoint k ph
  disjoint ph y
  disjoint ph z
  disjoint ., h
  disjoint ., i
  disjoint .x. e
  disjoint .x. h
  disjoint .x. i
  disjoint .x. y
  disjoint .x. z
  disjoint O h
  disjoint O i
  assert |- ( ph -> Y e. PreHil )

  proof
    wph
    vg
    vh
    vi
    cY
    cplusg
    cfv
    #
    cR
    cplusg
    cfv
    #
    cY
    cvsca
    cfv
    #
    c.x
    cR
    c.xi
    c.as
    cB
    c.0
    cV
    cY
    cO
    vk
    cV
    cY
    cbs
    cfv
    wceq
    wph
    frlmphl.v
    a1i
    wph
    @0
    eqidd
    wph
    @2
    eqidd
    c.xi
    cY
    cip
    cfv
    #
    wceq
    wph
    frlmphl.j
    a1i
    cO
    cY
    c0g
    cfv
    wceq
    wph
    frlmphl.o
    a1i
    wph
    cR
    cdr
    wcel
    #
    cI
    cW
    wcel
    #
    cR
    cY
    csca
    cfv
    #
    wceq
    #
    wph
    @4
    cR
    ccrg
    wcel
    #
    wph
    cR
    cfield
    wcel
    @4
    @8
    wa
    frlmphl.f
    cR
    isfld
    sylib
    #
    simpld
    #
    frlmphl.i
    cR
    cY
    cI
    cdr
    cW
    frlmphl.y
    frlmsca
    syl2anc
    #
    cB
    cR
    cbs
    cfv
    #
    wceq
    wph
    frlmphl.b
    a1i
    wph
    @1
    eqidd
    c.x
    cR
    cmulr
    cfv
    wceq
    wph
    frlmphl.t
    a1i
    c.as
    cR
    cstv
    cfv
    wceq
    wph
    frlmphl.s
    a1i
    c.0
    cR
    c0g
    cfv
    wceq
    wph
    frlmphl.0
    a1i
    wph
    cY
    clmod
    wcel
    #
    @6
    cdr
    wcel
    cY
    clvec
    wcel
    wph
    cR
    crg
    wcel
    #
    @5
    @13
    wph
    @4
    @14
    @10
    cR
    drngring
    syl
    #
    frlmphl.i
    cR
    cY
    cI
    cW
    frlmphl.y
    frlmlmod
    syl2anc
    #
    wph
    cR
    @6
    cdr
    @11
    @10
    eqeltrrd
    @6
    cY
    @6
    eqid
    #
    islvec
    sylanbrc
    wph
    vx
    cB
    cR
    c.as
    frlmphl.b
    frlmphl.s
    wph
    @4
    @8
    @9
    simprd
    #
    frlmphl.u
    idsrngd
    wph
    vg
    cv
    #
    cV
    wcel
    #
    vh
    cv
    #
    cV
    wcel
    #
    w3a
    #
    @19
    @21
    c.xi
    co
    #
    cR
    vx
    cI
    vx
    cv
    #
    @19
    cfv
    #
    @25
    @21
    cfv
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cB
    @23
    @24
    cR
    @19
    @21
    c.x
    cof
    #
    co
    #
    cgsu
    co
    #
    @30
    @23
    @5
    @14
    @20
    @22
    @24
    @33
    wceq
    wph
    @20
    @5
    @22
    frlmphl.i
    3ad2ant1
    #
    wph
    @20
    @14
    @22
    @15
    3ad2ant1
    #
    wph
    @20
    @22
    simp2
    #
    wph
    @20
    @22
    simp3
    #
    cB
    cR
    c.x
    @19
    @21
    c.xi
    cI
    cV
    cW
    crg
    cY
    frlmphl.y
    frlmphl.b
    frlmphl.t
    frlmphl.v
    frlmphl.j
    frlmipval
    syl22anc
    @23
    @32
    @29
    cR
    cgsu
    @23
    vx
    cI
    cI
    @26
    @27
    c.x
    cI
    @19
    @21
    cW
    cW
    @23
    cI
    cB
    @19
    wf
    #
    @19
    cI
    wfn
    @23
    @19
    cB
    cI
    cmap
    co
    #
    wcel
    #
    @38
    @23
    @5
    @20
    @40
    @34
    @36
    cV
    cR
    cY
    cI
    cB
    cW
    @19
    frlmphl.y
    frlmphl.b
    frlmphl.v
    frlmbasmap
    #
    syl2anc
    #
    @19
    cB
    cI
    elmapi
    #
    syl
    #
    cI
    cB
    @19
    ffn
    syl
    @23
    cI
    cB
    @21
    wf
    #
    @21
    cI
    wfn
    #
    @23
    @21
    @39
    wcel
    #
    @45
    @23
    @5
    @22
    @47
    @34
    @37
    cV
    cR
    cY
    cI
    cB
    cW
    @21
    frlmphl.y
    frlmphl.b
    frlmphl.v
    frlmbasmap
    #
    syl2anc
    #
    @21
    cB
    cI
    elmapi
    #
    syl
    #
    cI
    cB
    @21
    ffn
    #
    syl
    @34
    @34
    cI
    inidm
    #
    @23
    @25
    cI
    wcel
    #
    wa
    #
    @26
    eqidd
    @55
    @27
    eqidd
    offval
    oveq2d
    eqtrd
    #
    @23
    cI
    cB
    @29
    cR
    cW
    c.0
    frlmphl.b
    frlmphl.0
    wph
    @20
    cR
    ccmn
    wcel
    #
    @22
    wph
    @14
    @57
    @15
    cR
    ringcmn
    syl
    #
    3ad2ant1
    @34
    @23
    vx
    cI
    @28
    cB
    @29
    @55
    @14
    @26
    cB
    wcel
    #
    @27
    cB
    wcel
    #
    @28
    cB
    wcel
    @23
    @14
    @54
    @35
    adantr
    @23
    cI
    cB
    @25
    @19
    @44
    ffvelrnda
    #
    @23
    cI
    cB
    @25
    @21
    @51
    ffvelrnda
    #
    cB
    cR
    c.x
    @26
    @27
    frlmphl.b
    frlmphl.t
    ringcl
    syl3anc
    @29
    eqid
    fmptd
    wph
    vx
    cB
    cR
    c.x
    vg
    vh
    c.xi
    cI
    c.as
    cO
    cV
    cW
    cY
    c.0
    frlmphl.y
    frlmphl.b
    frlmphl.t
    frlmphl.v
    frlmphl.j
    frlmphl.o
    frlmphl.0
    frlmphl.s
    frlmphl.f
    frlmphl.m
    frlmphl.u
    frlmphl.i
    frlmphllem
    gsumcl
    eqeltrd
    #
    wph
    vk
    cv
    #
    cB
    wcel
    #
    @20
    @22
    vi
    cv
    #
    cV
    wcel
    #
    w3a
    #
    w3a
    #
    cR
    vx
    cI
    @64
    @26
    @25
    @66
    cfv
    #
    c.x
    co
    #
    c.x
    co
    #
    @27
    @70
    c.x
    co
    #
    @1
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cR
    vx
    cI
    @72
    cmpt
    #
    cgsu
    co
    #
    cR
    vx
    cI
    @73
    cmpt
    #
    cgsu
    co
    #
    @1
    co
    @64
    @19
    @2
    co
    #
    @21
    @0
    co
    #
    @66
    c.xi
    co
    #
    @64
    @19
    @66
    c.xi
    co
    #
    c.x
    co
    #
    @21
    @66
    c.xi
    co
    #
    @1
    co
    @69
    vx
    cI
    cB
    @72
    @73
    @1
    @77
    cR
    @79
    cW
    c.0
    frlmphl.b
    frlmphl.0
    @1
    eqid
    #
    wph
    @65
    @57
    @68
    @58
    3ad2ant1
    wph
    @65
    @5
    @68
    frlmphl.i
    3ad2ant1
    #
    @69
    @54
    wa
    #
    @14
    @65
    @71
    cB
    wcel
    #
    @72
    cB
    wcel
    @69
    @14
    @54
    wph
    @65
    @14
    @68
    @15
    3ad2ant1
    #
    adantr
    #
    @69
    @65
    @54
    wph
    @65
    @68
    simp2
    #
    adantr
    #
    @89
    @14
    @59
    @70
    cB
    wcel
    #
    @90
    @92
    @69
    cI
    cB
    @25
    @19
    @69
    @40
    @38
    @69
    @5
    @20
    @40
    @88
    wph
    @65
    @20
    @22
    @67
    simp31
    #
    @41
    syl2anc
    #
    @43
    syl
    ffvelrnda
    #
    @69
    cI
    cB
    @25
    @66
    @69
    @66
    @39
    wcel
    #
    cI
    cB
    @66
    wf
    #
    @69
    @5
    @67
    @99
    @88
    wph
    @65
    @20
    @22
    @67
    simp33
    #
    cV
    cR
    cY
    cI
    cB
    cW
    @66
    frlmphl.y
    frlmphl.b
    frlmphl.v
    frlmbasmap
    syl2anc
    #
    @66
    cB
    cI
    elmapi
    syl
    #
    ffvelrnda
    #
    cB
    cR
    c.x
    @26
    @70
    frlmphl.b
    frlmphl.t
    ringcl
    syl3anc
    #
    cB
    cR
    c.x
    @64
    @71
    frlmphl.b
    frlmphl.t
    ringcl
    syl3anc
    @89
    @14
    @60
    @95
    @73
    cB
    wcel
    @92
    @69
    cI
    cB
    @25
    @21
    @69
    @47
    @45
    @69
    @5
    @22
    @47
    @88
    wph
    @65
    @20
    @22
    @67
    simp32
    #
    @48
    syl2anc
    #
    @50
    syl
    #
    ffvelrnda
    #
    @104
    cB
    cR
    c.x
    @27
    @70
    frlmphl.b
    frlmphl.t
    ringcl
    syl3anc
    @69
    @77
    eqidd
    @69
    @79
    eqidd
    @69
    vx
    cI
    @64
    @26
    c.x
    co
    #
    cmpt
    #
    @66
    @31
    co
    #
    @77
    c.0
    cfsupp
    @69
    @112
    vy
    cI
    @64
    vy
    cv
    #
    @19
    cfv
    #
    c.x
    co
    #
    cmpt
    #
    @66
    @31
    co
    #
    @77
    @111
    @116
    @66
    @31
    vx
    vy
    cI
    @110
    @115
    vx
    vy
    weq
    @26
    @114
    @64
    c.x
    @25
    @113
    @19
    fveq2
    oveq2d
    cbvmptv
    #
    oveq1i
    @69
    @117
    vx
    cI
    @110
    @70
    c.x
    co
    #
    cmpt
    @77
    @69
    vx
    cI
    cI
    @110
    @70
    c.x
    cI
    @116
    @66
    cW
    cW
    @69
    @111
    cI
    wfn
    #
    @116
    cI
    wfn
    @69
    cI
    cB
    @111
    wf
    @120
    @69
    vx
    cI
    @110
    cB
    @111
    @89
    @14
    @65
    @59
    @110
    cB
    wcel
    #
    @92
    @94
    @98
    cB
    cR
    c.x
    @64
    @26
    frlmphl.b
    frlmphl.t
    ringcl
    syl3anc
    #
    @111
    eqid
    fmptd
    #
    cI
    cB
    @111
    ffn
    syl
    #
    cI
    @111
    @116
    @118
    fneq1i
    sylib
    @69
    @100
    @66
    cI
    wfn
    @103
    cI
    cB
    @66
    ffn
    syl
    #
    @88
    @88
    @53
    @89
    vy
    @25
    @115
    @110
    cI
    @116
    cvv
    @89
    @116
    eqidd
    @89
    vy
    vx
    weq
    #
    wa
    #
    @114
    @26
    @64
    c.x
    @127
    @113
    @25
    @19
    @89
    @126
    simpr
    fveq2d
    oveq2d
    @69
    @54
    simpr
    #
    @89
    @64
    @26
    c.x
    ovexd
    fvmptd
    @89
    @70
    eqidd
    offval
    @69
    vx
    cI
    @119
    @72
    @89
    @14
    @65
    @59
    @95
    @119
    @72
    wceq
    @92
    @94
    @98
    @104
    cB
    cR
    c.x
    @64
    @26
    @70
    frlmphl.b
    frlmphl.t
    ringass
    syl13anc
    #
    mpteq2dva
    eqtrd
    syl5eq
    @69
    @112
    cvv
    wcel
    @112
    wfun
    #
    @66
    c.0
    cfsupp
    wbr
    #
    @112
    c.0
    csupp
    co
    @66
    c.0
    csupp
    co
    wss
    @112
    c.0
    cfsupp
    wbr
    @69
    @111
    @66
    @31
    ovexd
    @69
    @130
    vz
    cI
    vz
    cv
    #
    @111
    cfv
    #
    @132
    @66
    cfv
    #
    c.x
    co
    #
    cmpt
    #
    wfun
    vz
    cI
    @135
    funmpt
    @69
    @112
    @136
    @69
    vz
    cI
    cI
    @133
    @134
    c.x
    cI
    @111
    @66
    cW
    cW
    @124
    @125
    @88
    @88
    @53
    @69
    @132
    cI
    wcel
    wa
    #
    @133
    eqidd
    @137
    @134
    eqidd
    offval
    funeqd
    mpbiri
    @69
    @5
    @67
    wa
    #
    @131
    wph
    @68
    @138
    @65
    wph
    @5
    @68
    @67
    frlmphl.i
    @20
    @22
    @67
    simp3
    anim12i
    3adant2
    cV
    cR
    cY
    cI
    cW
    @66
    c.0
    frlmphl.y
    frlmphl.0
    frlmphl.v
    frlmbasfsupp
    syl
    @69
    vy
    cI
    cB
    @111
    @66
    cW
    c.x
    c.0
    @88
    @69
    @14
    c.0
    cB
    wcel
    @91
    cB
    cR
    c.0
    frlmphl.b
    frlmphl.0
    ring0cl
    syl
    @123
    @103
    @69
    @14
    @113
    cB
    wcel
    @113
    c.0
    c.x
    co
    c.0
    wceq
    @91
    cB
    cR
    c.x
    @113
    c.0
    frlmphl.b
    frlmphl.t
    frlmphl.0
    ringrz
    sylan
    suppofss2d
    @66
    @112
    cvv
    c.0
    fsuppsssupp
    syl22anc
    eqbrtrrd
    @69
    wph
    @22
    @67
    @79
    c.0
    cfsupp
    wbr
    wph
    @65
    @68
    simp1
    #
    @106
    @101
    wph
    vx
    cB
    cR
    c.x
    vh
    vi
    c.xi
    cI
    c.as
    cO
    cV
    cW
    cY
    c.0
    frlmphl.y
    frlmphl.b
    frlmphl.t
    frlmphl.v
    frlmphl.j
    frlmphl.o
    frlmphl.0
    frlmphl.s
    frlmphl.f
    wph
    @20
    @19
    @19
    c.xi
    co
    #
    c.0
    wceq
    #
    w3a
    #
    @19
    cO
    wceq
    #
    wi
    wph
    @22
    @21
    @21
    c.xi
    co
    #
    c.0
    wceq
    #
    w3a
    #
    @21
    cO
    wceq
    #
    wi
    vg
    vh
    vg
    vh
    weq
    #
    @142
    @146
    @143
    @147
    @148
    @20
    @22
    @141
    @145
    wph
    @19
    @21
    cV
    eleq1
    @148
    @140
    @144
    c.0
    @148
    @19
    @21
    @19
    @21
    c.xi
    @148
    id
    #
    @149
    oveq12d
    eqeq1d
    3anbi23d
    @19
    @21
    cO
    eqeq1
    imbi12d
    frlmphl.m
    chvarv
    frlmphl.u
    frlmphl.i
    frlmphllem
    syl3anc
    gsummptfsadd
    @69
    @83
    cR
    vx
    cI
    @25
    @82
    cfv
    #
    @70
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @76
    @69
    ve
    vf
    @82
    @66
    @39
    @39
    cR
    vx
    cI
    @25
    ve
    cv
    #
    cfv
    #
    @25
    vf
    cv
    #
    cfv
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @153
    c.xi
    cvv
    wph
    @65
    c.xi
    ve
    vf
    @39
    @39
    @160
    cmpt2
    #
    wceq
    #
    @68
    wph
    c.xi
    vg
    vh
    @39
    @39
    @30
    cmpt2
    #
    @161
    wph
    @163
    @3
    c.xi
    wph
    @5
    @4
    @163
    @3
    wceq
    frlmphl.i
    @10
    vx
    cB
    cR
    c.x
    vg
    vh
    cI
    cdr
    cW
    cY
    frlmphl.y
    frlmphl.b
    frlmphl.t
    frlmip
    syl2anc
    frlmphl.j
    syl6reqr
    ve
    vf
    vg
    vh
    @39
    @39
    @160
    @30
    cR
    vx
    cI
    @26
    @157
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    ve
    vg
    weq
    #
    @159
    @165
    cR
    cgsu
    @166
    vx
    cI
    @158
    @164
    @166
    @155
    @26
    @157
    c.x
    @25
    @154
    @19
    fveq1
    oveq1d
    mpteq2dv
    oveq2d
    vf
    vh
    weq
    #
    @165
    @29
    cR
    cgsu
    @167
    vx
    cI
    @164
    @28
    @167
    @157
    @27
    @26
    c.x
    @25
    @156
    @21
    fveq1
    oveq2d
    mpteq2dv
    oveq2d
    cbvmpt2v
    syl6eqr
    #
    3ad2ant1
    #
    @69
    @154
    @82
    wceq
    #
    vf
    vi
    weq
    #
    wa
    wa
    #
    @159
    @152
    cR
    cgsu
    @172
    vx
    cI
    @158
    @151
    @172
    @155
    @150
    @157
    @70
    c.x
    @172
    @25
    @154
    @82
    @69
    @170
    @171
    simprl
    fveq1d
    @172
    @25
    @156
    @66
    @69
    @170
    @171
    simprr
    fveq1d
    oveq12d
    mpteq2dv
    oveq2d
    @69
    @5
    @82
    cV
    wcel
    #
    @82
    @39
    wcel
    @88
    @69
    @13
    @81
    cV
    wcel
    #
    @22
    @173
    wph
    @65
    @13
    @68
    @16
    3ad2ant1
    #
    @69
    @13
    @64
    @6
    cbs
    cfv
    #
    wcel
    @20
    @174
    @175
    @69
    @64
    cB
    @176
    @93
    @69
    cB
    @12
    @176
    frlmphl.b
    @69
    cR
    @6
    cbs
    wph
    @65
    @7
    @68
    @11
    3ad2ant1
    fveq2d
    syl5eq
    eleqtrd
    @96
    @64
    @2
    @6
    @176
    cV
    cY
    @19
    frlmphl.v
    @17
    @2
    eqid
    #
    @176
    eqid
    lmodvscl
    syl3anc
    #
    @106
    @0
    cV
    cY
    @81
    @21
    frlmphl.v
    @0
    eqid
    #
    lmodvacl
    syl3anc
    cV
    cR
    cY
    cI
    cB
    cW
    @82
    frlmphl.y
    frlmphl.b
    frlmphl.v
    frlmbasmap
    syl2anc
    @102
    @69
    cR
    @152
    cgsu
    ovexd
    ovmpt2d
    @69
    @152
    @75
    cR
    cgsu
    @69
    vx
    cI
    @151
    @74
    @89
    @151
    @110
    @27
    @1
    co
    #
    @70
    c.x
    co
    #
    @119
    @73
    @1
    co
    #
    @74
    @89
    @150
    @180
    @70
    c.x
    @69
    vx
    cI
    @180
    @82
    cvv
    @69
    @82
    @81
    @21
    @1
    cof
    co
    vx
    cI
    @180
    cmpt
    @69
    cV
    @1
    @0
    cR
    @81
    @21
    cI
    crg
    cW
    cY
    frlmphl.y
    frlmphl.v
    @91
    @88
    @178
    @106
    @87
    @179
    frlmplusgval
    @69
    vx
    cI
    cI
    @110
    @27
    @1
    cI
    @81
    @21
    cW
    cW
    @69
    @81
    @39
    wcel
    #
    cI
    cB
    @81
    wf
    @81
    cI
    wfn
    @69
    @5
    @174
    @183
    @88
    @178
    cV
    cR
    cY
    cI
    cB
    cW
    @81
    frlmphl.y
    frlmphl.b
    frlmphl.v
    frlmbasmap
    syl2anc
    @81
    cB
    cI
    elmapi
    cI
    cB
    @81
    ffn
    3syl
    @69
    @45
    @46
    @108
    @52
    syl
    @88
    @88
    @53
    @89
    @64
    cV
    cR
    @2
    c.x
    cI
    @25
    cB
    cW
    @19
    cY
    frlmphl.y
    frlmphl.v
    frlmphl.b
    @69
    @5
    @54
    @88
    adantr
    @94
    @69
    @20
    @54
    @96
    adantr
    @128
    @177
    frlmphl.t
    frlmvscaval
    @89
    @27
    eqidd
    offval
    eqtrd
    @89
    @110
    @27
    @1
    ovexd
    fvmpt2d
    oveq1d
    @89
    @14
    @121
    @60
    @95
    @181
    @182
    wceq
    @92
    @122
    @109
    @104
    cB
    @1
    cR
    c.x
    @110
    @27
    @70
    frlmphl.b
    @87
    frlmphl.t
    ringdir
    syl13anc
    @89
    @119
    @72
    @73
    @1
    @129
    oveq1d
    3eqtrd
    mpteq2dva
    oveq2d
    eqtrd
    @69
    @85
    @78
    @86
    @80
    @1
    @69
    @85
    @64
    cR
    vx
    cI
    @71
    cmpt
    #
    cgsu
    co
    #
    c.x
    co
    @78
    @69
    @84
    @185
    @64
    c.x
    @69
    ve
    vf
    @19
    @66
    @39
    @39
    @160
    @185
    c.xi
    cvv
    @169
    @69
    @166
    @171
    wa
    wa
    #
    @159
    @184
    cR
    cgsu
    @186
    vx
    cI
    @158
    @71
    @186
    @155
    @26
    @157
    @70
    c.x
    @186
    @25
    @154
    @19
    @69
    @166
    @171
    simprl
    fveq1d
    @186
    @25
    @156
    @66
    @69
    @166
    @171
    simprr
    fveq1d
    oveq12d
    mpteq2dv
    oveq2d
    @97
    @102
    @69
    cR
    @184
    cgsu
    ovexd
    ovmpt2d
    oveq2d
    @69
    cI
    cB
    @1
    cR
    c.x
    vx
    cW
    @71
    @64
    c.0
    frlmphl.b
    frlmphl.0
    @87
    frlmphl.t
    @91
    @88
    @93
    @105
    @69
    wph
    @20
    @67
    @184
    c.0
    cfsupp
    wbr
    @139
    @96
    @101
    wph
    vx
    cB
    cR
    c.x
    vg
    vi
    c.xi
    cI
    c.as
    cO
    cV
    cW
    cY
    c.0
    frlmphl.y
    frlmphl.b
    frlmphl.t
    frlmphl.v
    frlmphl.j
    frlmphl.o
    frlmphl.0
    frlmphl.s
    frlmphl.f
    frlmphl.m
    frlmphl.u
    frlmphl.i
    frlmphllem
    syl3anc
    gsummulc2
    eqtr4d
    @69
    ve
    vf
    @21
    @66
    @39
    @39
    @160
    @80
    c.xi
    cvv
    @169
    @69
    ve
    vh
    weq
    #
    @171
    wa
    wa
    #
    @159
    @79
    cR
    cgsu
    @188
    vx
    cI
    @158
    @73
    @188
    @155
    @27
    @157
    @70
    c.x
    @188
    @25
    @154
    @21
    @69
    @187
    @171
    simprl
    fveq1d
    @188
    @25
    @156
    @66
    @69
    @187
    @171
    simprr
    fveq1d
    oveq12d
    mpteq2dv
    oveq2d
    @107
    @102
    @69
    cR
    @79
    cgsu
    ovexd
    ovmpt2d
    oveq12d
    3eqtr4d
    frlmphl.m
    @23
    cR
    vx
    cI
    @27
    @26
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @30
    @21
    @19
    c.xi
    co
    @24
    c.as
    cfv
    #
    @23
    @190
    @29
    cR
    cgsu
    @23
    vx
    cI
    @189
    @28
    @55
    @8
    @60
    @59
    @189
    @28
    wceq
    @23
    @8
    @54
    wph
    @20
    @8
    @22
    @18
    3ad2ant1
    adantr
    @62
    @61
    cB
    cR
    c.x
    @27
    @26
    frlmphl.b
    frlmphl.t
    crngcom
    syl3anc
    mpteq2dva
    oveq2d
    @23
    ve
    vf
    @21
    @19
    @39
    @39
    @160
    @191
    c.xi
    cvv
    wph
    @20
    @162
    @22
    @168
    3ad2ant1
    @23
    @187
    vf
    vg
    weq
    #
    wa
    wa
    #
    @159
    @190
    cR
    cgsu
    @194
    vx
    cI
    @158
    @189
    @194
    @155
    @27
    @157
    @26
    c.x
    @194
    @25
    @154
    @21
    @23
    @187
    @193
    simprl
    fveq1d
    @194
    @25
    @156
    @19
    @23
    @187
    @193
    simprr
    fveq1d
    oveq12d
    mpteq2dv
    oveq2d
    @49
    @42
    @23
    cR
    @190
    cgsu
    ovexd
    ovmpt2d
    @23
    @192
    @24
    @30
    @23
    @24
    cB
    wcel
    @25
    c.as
    cfv
    #
    @25
    wceq
    #
    vx
    cB
    wral
    #
    @192
    @24
    wceq
    #
    @63
    wph
    @20
    @197
    @22
    wph
    @196
    vx
    cB
    frlmphl.u
    ralrimiva
    3ad2ant1
    @196
    @198
    vx
    @24
    cB
    @25
    @24
    wceq
    #
    @195
    @192
    @25
    @24
    @25
    @24
    c.as
    fveq2
    @199
    id
    eqeq12d
    rspcv
    sylc
    @56
    eqtrd
    3eqtr4rd
    isphld
end
