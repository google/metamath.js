include "cress.mm"
include "co.mm"
include "cgrp.mm"
include "wcel.mm"
include "cqs.mm"
include "cvv.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cxp.mm"
include "wf.mm"
include "c0g.mm"
include "cv.mm"
include "wceq.mm"
include "cplusg.mm"
include "wral.mm"
include "cga.mm"
include "csubg.mm"
include "eqid.mm"
include "subggrp.mm"
include "syl.mm"
include "cpw.mm"
include "cfn.mm"
include "pwfi.mm"
include "sylib.mm"
include "wer.mm"
include "eqger.mm"
include "qsss.mm"
include "ssexd.mm"
include "jca.mm"
include "wfn.mm"
include "cmpt.mm"
include "crn.mm"
include "vex.mm"
include "mptex.mm"
include "rnex.mm"
include "fnmpt2i.mm"
include "a1i.mm"
include "cec.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "w3a.mm"
include "sylow2blem1.mm"
include "cqg.mm"
include "ovex.mm"
include "eqeltri.mm"
include "subgrcl.mm"
include "3ad2ant1.mm"
include "wss.mm"
include "subgss.mm"
include "sselda.mm"
include "3adant3.mm"
include "simp3.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "ecelqsg.mm"
include "sylancr.mm"
include "eqeltrd.mm"
include "3expa.mm"
include "ectocld.mm"
include "ralrimiva.mm"
include "ffnov.mm"
include "sylanbrc.mm"
include "subgbas.mm"
include "xpeq1d.mm"
include "feq2d.mm"
include "mpbid.mm"
include "id.mm"
include "eqeq12d.mm"
include "oveq2d.mm"
include "2ralbidv.mm"
include "anbi12d.mm"
include "simpl.mm"
include "adantr.mm"
include "subg0cl.mm"
include "simpr.mm"
include "subg0.mm"
include "oveq1d.mm"
include "grplid.mm"
include "sylan.mm"
include "eceq1d.mm"
include "3eqtr3d.mm"
include "simprl.mm"
include "sseldd.mm"
include "simprr.mm"
include "grpass.mm"
include "syl13anc.mm"
include "eqtr4d.mm"
include "subgcl.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "ressplusg.mm"
include "oveqdr.mm"
include "eqeq1d.mm"
include "raleqbidv.mm"
include "isga.mm"

theorem sylow2blem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.pl: class .+
  let c.sm: class .~
  let c.x: class .x.
  let cG: class G
  let cH: class H
  let cK: class K
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let c.mi: class .-
  let cB: class B
  let cC: class C
  assume sylow2b.x: |- X = ( Base ` G )
  assume sylow2b.xf: |- ( ph -> X e. Fin )
  assume sylow2b.h: |- ( ph -> H e. ( SubGrp ` G ) )
  assume sylow2b.k: |- ( ph -> K e. ( SubGrp ` G ) )
  assume sylow2b.a: |- .+ = ( +g ` G )
  assume sylow2b.r: |- .~ = ( G ~QG K )
  assume sylow2b.m: |- .x. = ( x e. H , y e. ( X /. .~ ) |-> ran ( z e. y |-> ( x .+ z ) ) )

  disjoint x y
  disjoint x z
  disjoint G x
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint .x. x
  disjoint .x. y
  disjoint .x. z
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint .~ x
  disjoint .~ y
  disjoint .~ z
  disjoint ph z
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint a b
  disjoint a g
  disjoint a s
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint G a
  disjoint b g
  disjoint b s
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint G b
  disjoint g s
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint G g
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint G s
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint G u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint G v
  disjoint K g
  disjoint K u
  disjoint K v
  disjoint .x. a
  disjoint .x. b
  disjoint .x. g
  disjoint .x. s
  disjoint .x. u
  disjoint .x. v
  disjoint .+ g
  disjoint .+ s
  disjoint .+ u
  disjoint .+ v
  disjoint .~ a
  disjoint .~ b
  disjoint .~ g
  disjoint .~ s
  disjoint .~ u
  disjoint .~ v
  disjoint a ph
  disjoint b ph
  disjoint g ph
  disjoint ph s
  disjoint ph u
  disjoint ph v
  disjoint .- u
  disjoint .- x
  disjoint .- z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint H a
  disjoint H b
  disjoint H g
  disjoint H s
  disjoint H u
  disjoint H v
  disjoint X a
  disjoint X b
  disjoint X g
  disjoint X s
  disjoint X u
  disjoint X v
  assert |- ( ph -> .x. e. ( ( G |`s H ) GrpAct ( X /. .~ ) ) )

  proof
    wph
    cG
    cH
    cress
    co
    #
    cgrp
    wcel
    #
    cX
    c.sm
    cqs
    #
    cvv
    wcel
    #
    wa
    @0
    cbs
    cfv
    #
    @2
    cxp
    #
    @2
    c.x
    wf
    #
    @0
    c0g
    cfv
    #
    vu
    cv
    #
    c.x
    co
    #
    @8
    wceq
    #
    va
    cv
    #
    vb
    cv
    #
    @0
    cplusg
    cfv
    #
    co
    #
    @8
    c.x
    co
    #
    @11
    @12
    @8
    c.x
    co
    #
    c.x
    co
    #
    wceq
    #
    vb
    @4
    wral
    va
    @4
    wral
    #
    wa
    #
    vu
    @2
    wral
    #
    wa
    c.x
    @0
    @2
    cga
    co
    wcel
    wph
    @1
    @3
    wph
    cH
    cG
    csubg
    cfv
    #
    wcel
    #
    @1
    sylow2b.h
    cH
    cG
    @0
    @0
    eqid
    #
    subggrp
    syl
    wph
    @2
    cX
    cpw
    #
    cfn
    wph
    cX
    cfn
    wcel
    @25
    cfn
    wcel
    sylow2b.xf
    cX
    pwfi
    sylib
    wph
    cX
    c.sm
    wph
    cK
    @22
    wcel
    cX
    c.sm
    wer
    sylow2b.k
    c.sm
    cG
    cX
    cK
    sylow2b.x
    sylow2b.r
    eqger
    syl
    qsss
    ssexd
    jca
    wph
    @6
    @21
    wph
    cH
    @2
    cxp
    #
    @2
    c.x
    wf
    #
    @6
    wph
    c.x
    @26
    wfn
    #
    @8
    vv
    cv
    #
    c.x
    co
    #
    @2
    wcel
    #
    vv
    @2
    wral
    #
    vu
    cH
    wral
    @27
    @28
    wph
    vx
    vy
    cH
    @2
    vz
    vy
    cv
    #
    vx
    cv
    vz
    cv
    c.pl
    co
    #
    cmpt
    #
    crn
    c.x
    sylow2b.m
    @35
    vz
    @33
    @34
    vy
    vex
    mptex
    rnex
    fnmpt2i
    a1i
    wph
    @32
    vu
    cH
    wph
    @8
    cH
    wcel
    #
    wa
    #
    @31
    vv
    @2
    @8
    vs
    cv
    #
    c.sm
    cec
    #
    c.x
    co
    #
    @2
    wcel
    #
    @31
    @37
    vs
    @29
    cX
    c.sm
    @2
    @2
    eqid
    #
    @39
    @29
    wceq
    @40
    @30
    @2
    @39
    @29
    @8
    c.x
    oveq2
    eleq1d
    wph
    @36
    @38
    cX
    wcel
    #
    @41
    wph
    @36
    @43
    w3a
    #
    @40
    @8
    @38
    c.pl
    co
    #
    c.sm
    cec
    #
    @2
    wph
    vx
    vy
    vz
    @8
    @38
    c.pl
    c.sm
    c.x
    cG
    cH
    cK
    cX
    sylow2b.x
    sylow2b.xf
    sylow2b.h
    sylow2b.k
    sylow2b.a
    sylow2b.r
    sylow2b.m
    sylow2blem1
    @44
    c.sm
    cvv
    wcel
    @45
    cX
    wcel
    #
    @46
    @2
    wcel
    c.sm
    cG
    cK
    cqg
    co
    cvv
    sylow2b.r
    cG
    cK
    cqg
    ovex
    eqeltri
    @44
    cG
    cgrp
    wcel
    #
    @8
    cX
    wcel
    #
    @43
    @47
    wph
    @36
    @48
    @43
    wph
    @23
    @48
    sylow2b.h
    cH
    cG
    subgrcl
    #
    syl
    #
    3ad2ant1
    wph
    @36
    @49
    @43
    wph
    cH
    cX
    @8
    wph
    @23
    cH
    cX
    wss
    #
    sylow2b.h
    cX
    cH
    cG
    sylow2b.x
    subgss
    #
    syl
    sselda
    3adant3
    wph
    @36
    @43
    simp3
    cX
    c.pl
    cG
    @8
    @38
    sylow2b.x
    sylow2b.a
    grpcl
    syl3anc
    cX
    @45
    c.sm
    cvv
    ecelqsg
    sylancr
    eqeltrd
    3expa
    ectocld
    ralrimiva
    ralrimiva
    vu
    vv
    cH
    @2
    @2
    c.x
    ffnov
    sylanbrc
    wph
    @26
    @5
    @2
    c.x
    wph
    cH
    @4
    @2
    wph
    @23
    cH
    @4
    wceq
    #
    sylow2b.h
    cH
    cG
    @0
    @24
    subgbas
    #
    syl
    xpeq1d
    feq2d
    mpbid
    wph
    @20
    vu
    @2
    @7
    @39
    c.x
    co
    #
    @39
    wceq
    #
    @14
    @39
    c.x
    co
    #
    @11
    @12
    @39
    c.x
    co
    #
    c.x
    co
    #
    wceq
    #
    vb
    @4
    wral
    #
    va
    @4
    wral
    #
    wa
    @20
    wph
    vs
    @8
    cX
    c.sm
    @2
    @42
    @39
    @8
    wceq
    #
    @57
    @10
    @63
    @19
    @64
    @56
    @9
    @39
    @8
    @39
    @8
    @7
    c.x
    oveq2
    @64
    id
    eqeq12d
    @64
    @61
    @18
    va
    vb
    @4
    @4
    @64
    @58
    @15
    @60
    @17
    @39
    @8
    @14
    c.x
    oveq2
    @64
    @59
    @16
    @11
    c.x
    @39
    @8
    @12
    c.x
    oveq2
    oveq2d
    eqeq12d
    2ralbidv
    anbi12d
    wph
    @43
    wa
    #
    @57
    @63
    @65
    cG
    c0g
    cfv
    #
    @39
    c.x
    co
    #
    @66
    @38
    c.pl
    co
    #
    c.sm
    cec
    #
    @56
    @39
    @65
    wph
    @66
    cH
    wcel
    #
    @43
    @67
    @69
    wceq
    wph
    @43
    simpl
    #
    @65
    @23
    @70
    wph
    @23
    @43
    sylow2b.h
    adantr
    #
    cH
    cG
    @66
    @66
    eqid
    #
    subg0cl
    syl
    wph
    @43
    simpr
    #
    wph
    vx
    vy
    vz
    @66
    @38
    c.pl
    c.sm
    c.x
    cG
    cH
    cK
    cX
    sylow2b.x
    sylow2b.xf
    sylow2b.h
    sylow2b.k
    sylow2b.a
    sylow2b.r
    sylow2b.m
    sylow2blem1
    syl3anc
    @65
    @66
    @7
    @39
    c.x
    @65
    @23
    @66
    @7
    wceq
    @72
    cH
    cG
    @0
    @66
    @24
    @73
    subg0
    syl
    oveq1d
    @65
    @68
    @38
    c.sm
    wph
    @48
    @43
    @68
    @38
    wceq
    @51
    cX
    c.pl
    cG
    @38
    @66
    sylow2b.x
    sylow2b.a
    @73
    grplid
    sylan
    eceq1d
    3eqtr3d
    @65
    @11
    @12
    c.pl
    co
    #
    @39
    c.x
    co
    #
    @60
    wceq
    #
    vb
    cH
    wral
    #
    va
    cH
    wral
    @63
    @65
    @77
    va
    vb
    cH
    cH
    @65
    @11
    cH
    wcel
    #
    @12
    cH
    wcel
    #
    wa
    #
    wa
    #
    @75
    @38
    c.pl
    co
    #
    c.sm
    cec
    #
    @11
    @12
    @38
    c.pl
    co
    #
    c.sm
    cec
    #
    c.x
    co
    #
    @76
    @60
    @82
    @84
    @11
    @85
    c.pl
    co
    #
    c.sm
    cec
    #
    @87
    @82
    @83
    @88
    c.sm
    @82
    @48
    @11
    cX
    wcel
    @12
    cX
    wcel
    #
    @43
    @83
    @88
    wceq
    @82
    @23
    @48
    @65
    @23
    @81
    @72
    adantr
    #
    @50
    syl
    #
    @82
    cH
    cX
    @11
    @82
    @23
    @52
    @91
    @53
    syl
    #
    @65
    @79
    @80
    simprl
    #
    sseldd
    @82
    cH
    cX
    @12
    @93
    @65
    @79
    @80
    simprr
    #
    sseldd
    #
    @65
    @43
    @81
    @74
    adantr
    #
    cX
    c.pl
    cG
    @11
    @12
    @38
    sylow2b.x
    sylow2b.a
    grpass
    syl13anc
    eceq1d
    @82
    wph
    @79
    @85
    cX
    wcel
    #
    @87
    @89
    wceq
    @65
    wph
    @81
    @71
    adantr
    #
    @94
    @82
    @48
    @90
    @43
    @98
    @92
    @96
    @97
    cX
    c.pl
    cG
    @12
    @38
    sylow2b.x
    sylow2b.a
    grpcl
    syl3anc
    wph
    vx
    vy
    vz
    @11
    @85
    c.pl
    c.sm
    c.x
    cG
    cH
    cK
    cX
    sylow2b.x
    sylow2b.xf
    sylow2b.h
    sylow2b.k
    sylow2b.a
    sylow2b.r
    sylow2b.m
    sylow2blem1
    syl3anc
    eqtr4d
    @82
    wph
    @75
    cH
    wcel
    #
    @43
    @76
    @84
    wceq
    @99
    @82
    @23
    @79
    @80
    @100
    @91
    @94
    @95
    c.pl
    cH
    cG
    @11
    @12
    sylow2b.a
    subgcl
    syl3anc
    @97
    wph
    vx
    vy
    vz
    @75
    @38
    c.pl
    c.sm
    c.x
    cG
    cH
    cK
    cX
    sylow2b.x
    sylow2b.xf
    sylow2b.h
    sylow2b.k
    sylow2b.a
    sylow2b.r
    sylow2b.m
    sylow2blem1
    syl3anc
    @82
    @59
    @86
    @11
    c.x
    @82
    wph
    @80
    @43
    @59
    @86
    wceq
    @99
    @95
    @97
    wph
    vx
    vy
    vz
    @12
    @38
    c.pl
    c.sm
    c.x
    cG
    cH
    cK
    cX
    sylow2b.x
    sylow2b.xf
    sylow2b.h
    sylow2b.k
    sylow2b.a
    sylow2b.r
    sylow2b.m
    sylow2blem1
    syl3anc
    oveq2d
    3eqtr4d
    ralrimivva
    @65
    @78
    @62
    va
    cH
    @4
    @65
    @23
    @54
    @72
    @55
    syl
    #
    @65
    @77
    @61
    vb
    cH
    @4
    @101
    @65
    @76
    @58
    @60
    @65
    @75
    @14
    @39
    c.x
    wph
    @43
    va
    vb
    c.pl
    @13
    wph
    @23
    c.pl
    @13
    wceq
    sylow2b.h
    cH
    c.pl
    cG
    @0
    @22
    @24
    sylow2b.a
    ressplusg
    syl
    oveqdr
    oveq1d
    eqeq1d
    raleqbidv
    raleqbidv
    mpbid
    jca
    ectocld
    ralrimiva
    jca
    vu
    va
    vb
    @13
    c.x
    @0
    @4
    @2
    @7
    @4
    eqid
    @13
    eqid
    @7
    eqid
    isga
    sylanbrc
end
