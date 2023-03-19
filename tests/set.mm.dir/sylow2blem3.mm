include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cqs.mm"
include "wrex.mm"
include "cmpt.mm"
include "crn.mm"
include "wss.mm"
include "cress.mm"
include "cbs.mm"
include "cfv.mm"
include "crab.mm"
include "c0.mm"
include "wne.mm"
include "chash.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "cpc.mm"
include "cexp.mm"
include "cdiv.mm"
include "cprime.mm"
include "wcel.mm"
include "cn.mm"
include "cpgp.mm"
include "pgpprm.mm"
include "syl.mm"
include "cgrp.mm"
include "csubg.mm"
include "subgrcl.mm"
include "grpbn0.mm"
include "cfn.mm"
include "wb.mm"
include "hashnncl.mm"
include "mpbird.mm"
include "pcndvds2.mm"
include "syl2anc.mm"
include "cmul.mm"
include "lagsubg2.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "cn0.mm"
include "cpw.mm"
include "pwfi.mm"
include "sylib.mm"
include "wer.mm"
include "eqger.mm"
include "qsss.mm"
include "ssfi.mm"
include "hashcl.mm"
include "nn0cnd.mm"
include "c0g.mm"
include "eqid.mm"
include "subg0cl.mm"
include "ne0i.mm"
include "subgss.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcan4d.mm"
include "3eqtr3d.mm"
include "breq2d.mm"
include "mtbid.mm"
include "cz.mm"
include "cmin.mm"
include "prmz.mm"
include "nn0zd.mm"
include "ssrab2.mm"
include "sylancl.mm"
include "cpr.mm"
include "wa.mm"
include "copab.mm"
include "sylow2blem2.mm"
include "subgbas.mm"
include "eqeltrrd.mm"
include "sylow2a.mm"
include "dvdssub2.mm"
include "syl31anc.mm"
include "cc0.mm"
include "hasheq0.mm"
include "dvds0.mm"
include "breq2.mm"
include "syl5ibrcom.mm"
include "sylbird.mm"
include "necon3bd.mm"
include "mpd.mm"
include "rabn0.mm"
include "raleqdv.mm"
include "rexbidv.mm"
include "cec.mm"
include "wi.mm"
include "vex.mm"
include "elqs.mm"
include "cminusg.mm"
include "w3a.mm"
include "simplrr.mm"
include "simprr.mm"
include "simpll.mm"
include "simprl.mm"
include "simplrl.mm"
include "sylow2blem1.mm"
include "syl3anc.mm"
include "eqtr3d.mm"
include "ad2antrr.mm"
include "erth.mm"
include "eqgval.mm"
include "mpbid.mm"
include "simp3d.mm"
include "oveq2.mm"
include "ovex.mm"
include "fvmpt.mm"
include "grprinv.mm"
include "grpinvcl.mm"
include "sseldd.mm"
include "grpcl.mm"
include "grpass.mm"
include "syl13anc.mm"
include "grplid.mm"
include "grppncan.mm"
include "3eqtrd.mm"
include "wfn.mm"
include "fnmpti.mm"
include "fnfvelrn.mm"
include "sylancr.mm"
include "expr.mm"
include "ralimdva.mm"
include "imp.mm"
include "an32s.mm"
include "dfss3.mm"
include "sylibr.mm"
include "reximdva.mm"
include "ex.mm"
include "com23.mm"
include "syl5bi.mm"
include "rexlimdv.mm"

theorem sylow2blem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let c.pl: class .+
  let c.sm: class .~
  let c.x: class .x.
  let vg: setvar g
  let cG: class G
  let cH: class H
  let cK: class K
  let c.mi: class .-
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let cB: class B
  let cC: class C
  assume sylow2b.x: |- X = ( Base ` G )
  assume sylow2b.xf: |- ( ph -> X e. Fin )
  assume sylow2b.h: |- ( ph -> H e. ( SubGrp ` G ) )
  assume sylow2b.k: |- ( ph -> K e. ( SubGrp ` G ) )
  assume sylow2b.a: |- .+ = ( +g ` G )
  assume sylow2b.r: |- .~ = ( G ~QG K )
  assume sylow2b.m: |- .x. = ( x e. H , y e. ( X /. .~ ) |-> ran ( z e. y |-> ( x .+ z ) ) )
  assume sylow2blem3.hp: |- ( ph -> P pGrp ( G |`s H ) )
  assume sylow2blem3.kn: |- ( ph -> ( # ` K ) = ( P ^ ( P pCnt ( # ` X ) ) ) )
  assume sylow2blem3.d: |- .- = ( -g ` G )

  disjoint g x
  disjoint g y
  disjoint g z
  disjoint G g
  disjoint x y
  disjoint x z
  disjoint G x
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint K g
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint .x. g
  disjoint .x. x
  disjoint .x. y
  disjoint .x. z
  disjoint .+ g
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint .~ g
  disjoint .~ x
  disjoint .~ y
  disjoint .~ z
  disjoint g ph
  disjoint ph z
  disjoint .- x
  disjoint .- z
  disjoint H g
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint X g
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
  disjoint K u
  disjoint K v
  disjoint .x. a
  disjoint .x. b
  disjoint .x. s
  disjoint .x. u
  disjoint .x. v
  disjoint .+ s
  disjoint .+ u
  disjoint .+ v
  disjoint .~ a
  disjoint .~ b
  disjoint .~ s
  disjoint .~ u
  disjoint .~ v
  disjoint a ph
  disjoint b ph
  disjoint ph s
  disjoint ph u
  disjoint ph v
  disjoint .- u
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint H a
  disjoint H b
  disjoint H s
  disjoint H u
  disjoint H v
  disjoint X a
  disjoint X b
  disjoint X s
  disjoint X u
  disjoint X v
  assert |- ( ph -> E. g e. X H C_ ran ( x e. K |-> ( ( g .+ x ) .- g ) ) )

  proof
    wph
    vu
    cv
    #
    vz
    cv
    #
    c.x
    co
    #
    @1
    wceq
    #
    vu
    cH
    wral
    #
    vz
    cX
    c.sm
    cqs
    #
    wrex
    #
    cH
    vx
    cK
    vg
    cv
    #
    vx
    cv
    #
    c.pl
    co
    #
    @7
    c.mi
    co
    #
    cmpt
    #
    crn
    #
    wss
    #
    vg
    cX
    wrex
    #
    wph
    @6
    @3
    vu
    cG
    cH
    cress
    co
    #
    cbs
    cfv
    #
    wral
    #
    vz
    @5
    wrex
    #
    wph
    @17
    vz
    @5
    crab
    #
    c0
    wne
    #
    @18
    wph
    cP
    @19
    chash
    cfv
    #
    cdvds
    wbr
    #
    wn
    @20
    wph
    cP
    @5
    chash
    cfv
    #
    cdvds
    wbr
    #
    @22
    wph
    cP
    cX
    chash
    cfv
    #
    cP
    cP
    @25
    cpc
    co
    cexp
    co
    #
    cdiv
    co
    #
    cdvds
    wbr
    #
    @24
    wph
    cP
    cprime
    wcel
    #
    @25
    cn
    wcel
    #
    @28
    wn
    wph
    cP
    @15
    cpgp
    wbr
    @29
    sylow2blem3.hp
    cP
    @15
    pgpprm
    syl
    #
    wph
    @30
    cX
    c0
    wne
    #
    wph
    cG
    cgrp
    wcel
    #
    @32
    wph
    cH
    cG
    csubg
    cfv
    #
    wcel
    #
    @33
    sylow2b.h
    cH
    cG
    subgrcl
    syl
    #
    cX
    cG
    sylow2b.x
    grpbn0
    syl
    wph
    cX
    cfn
    wcel
    #
    @30
    @32
    wb
    sylow2b.xf
    cX
    hashnncl
    syl
    mpbird
    cP
    @25
    pcndvds2
    syl2anc
    wph
    @27
    @23
    cP
    cdvds
    wph
    @25
    cK
    chash
    cfv
    #
    cdiv
    co
    @23
    @38
    cmul
    co
    #
    @38
    cdiv
    co
    @27
    @23
    wph
    @25
    @39
    @38
    cdiv
    wph
    c.sm
    cG
    cX
    cK
    sylow2b.x
    sylow2b.r
    sylow2b.k
    sylow2b.xf
    lagsubg2
    oveq1d
    wph
    @38
    @26
    @25
    cdiv
    sylow2blem3.kn
    oveq2d
    wph
    @23
    @38
    wph
    @23
    wph
    @5
    cfn
    wcel
    #
    @23
    cn0
    wcel
    wph
    cX
    cpw
    #
    cfn
    wcel
    #
    @5
    @41
    wss
    @40
    wph
    @37
    @42
    sylow2b.xf
    cX
    pwfi
    sylib
    wph
    cX
    c.sm
    wph
    cK
    @34
    wcel
    #
    cX
    c.sm
    wer
    #
    sylow2b.k
    c.sm
    cG
    cX
    cK
    sylow2b.x
    sylow2b.r
    eqger
    syl
    #
    qsss
    @41
    @5
    ssfi
    syl2anc
    #
    @5
    hashcl
    syl
    #
    nn0cnd
    wph
    @38
    wph
    @38
    cn
    wcel
    #
    cK
    c0
    wne
    #
    wph
    cG
    c0g
    cfv
    #
    cK
    wcel
    #
    @49
    wph
    @43
    @51
    sylow2b.k
    cK
    cG
    @50
    @50
    eqid
    #
    subg0cl
    syl
    cK
    @50
    ne0i
    syl
    wph
    cK
    cfn
    wcel
    #
    @48
    @49
    wb
    wph
    @37
    cK
    cX
    wss
    #
    @53
    sylow2b.xf
    wph
    @43
    @54
    sylow2b.k
    cX
    cK
    cG
    sylow2b.x
    subgss
    syl
    #
    cX
    cK
    ssfi
    syl2anc
    cK
    hashnncl
    syl
    mpbird
    #
    nncnd
    wph
    @38
    @56
    nnne0d
    divcan4d
    3eqtr3d
    breq2d
    mtbid
    wph
    cP
    cz
    wcel
    #
    @23
    cz
    wcel
    @21
    cz
    wcel
    cP
    @23
    @21
    cmin
    co
    cdvds
    wbr
    @24
    @22
    wb
    wph
    @29
    @57
    @31
    cP
    prmz
    syl
    #
    wph
    @23
    @47
    nn0zd
    wph
    @21
    wph
    @19
    cfn
    wcel
    #
    @21
    cn0
    wcel
    wph
    @40
    @19
    @5
    wss
    @59
    @46
    @17
    vz
    @5
    ssrab2
    @5
    @19
    ssfi
    sylancl
    #
    @19
    hashcl
    syl
    nn0zd
    wph
    vx
    vy
    vz
    cP
    c.x
    @8
    vy
    cv
    #
    cpr
    @5
    wss
    @7
    @8
    c.x
    co
    @61
    wceq
    vg
    @16
    wrex
    wa
    vx
    vy
    copab
    #
    vg
    vu
    @15
    @16
    @5
    @19
    @16
    eqid
    wph
    vx
    vy
    vz
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
    sylow2blem2
    sylow2blem3.hp
    wph
    cH
    @16
    cfn
    wph
    @35
    cH
    @16
    wceq
    sylow2b.h
    cH
    cG
    @15
    @15
    eqid
    subgbas
    syl
    #
    wph
    @37
    cH
    cX
    wss
    #
    cH
    cfn
    wcel
    sylow2b.xf
    wph
    @35
    @64
    sylow2b.h
    cX
    cH
    cG
    sylow2b.x
    subgss
    syl
    #
    cX
    cH
    ssfi
    syl2anc
    eqeltrrd
    @46
    @19
    eqid
    @62
    eqid
    sylow2a
    cP
    @23
    @21
    dvdssub2
    syl31anc
    mtbid
    wph
    @22
    @19
    c0
    wph
    @19
    c0
    wceq
    #
    @21
    cc0
    wceq
    #
    @22
    wph
    @59
    @67
    @66
    wb
    @60
    @19
    cfn
    hasheq0
    syl
    wph
    @22
    @67
    cP
    cc0
    cdvds
    wbr
    #
    wph
    @57
    @68
    @58
    cP
    dvds0
    syl
    @21
    cc0
    cP
    cdvds
    breq2
    syl5ibrcom
    sylbird
    necon3bd
    mpd
    @17
    vz
    @5
    rabn0
    sylib
    wph
    @4
    @17
    vz
    @5
    wph
    @3
    vu
    cH
    @16
    @63
    raleqdv
    rexbidv
    mpbird
    wph
    @4
    @14
    vz
    @5
    @1
    @5
    wcel
    @1
    @7
    c.sm
    cec
    #
    wceq
    #
    vg
    cX
    wrex
    #
    wph
    @4
    @14
    wi
    vg
    cX
    @1
    c.sm
    vz
    vex
    elqs
    wph
    @4
    @71
    @14
    wph
    @4
    @71
    @14
    wi
    wph
    @4
    wa
    #
    @70
    @13
    vg
    cX
    @72
    @7
    cX
    wcel
    #
    @70
    @13
    @72
    @73
    @70
    wa
    #
    wa
    @0
    @12
    wcel
    #
    vu
    cH
    wral
    #
    @13
    wph
    @74
    @4
    @76
    wph
    @74
    wa
    #
    @4
    @76
    @77
    @3
    @75
    vu
    cH
    @77
    @0
    cH
    wcel
    #
    @3
    @75
    @77
    @78
    @3
    wa
    #
    wa
    #
    @7
    cG
    cminusg
    cfv
    #
    cfv
    #
    @0
    @7
    c.pl
    co
    #
    c.pl
    co
    #
    @11
    cfv
    #
    @0
    @12
    @80
    @85
    @7
    @84
    c.pl
    co
    #
    @7
    c.mi
    co
    #
    @83
    @7
    c.mi
    co
    #
    @0
    @80
    @84
    cK
    wcel
    #
    @85
    @87
    wceq
    @80
    @73
    @83
    cX
    wcel
    #
    @89
    @80
    @7
    @83
    c.sm
    wbr
    #
    @73
    @90
    @89
    w3a
    #
    @80
    @91
    @69
    @83
    c.sm
    cec
    #
    wceq
    @80
    @1
    @69
    @93
    wph
    @73
    @70
    @79
    simplrr
    #
    @80
    @2
    @0
    @69
    c.x
    co
    #
    @1
    @93
    @80
    @1
    @69
    @0
    c.x
    @94
    oveq2d
    @77
    @78
    @3
    simprr
    @80
    wph
    @78
    @73
    @95
    @93
    wceq
    wph
    @74
    @79
    simpll
    @77
    @78
    @3
    simprl
    #
    wph
    @73
    @70
    @79
    simplrl
    #
    wph
    vx
    vy
    vz
    @0
    @7
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
    3eqtr3d
    eqtr3d
    @80
    @7
    @83
    c.sm
    cX
    wph
    @44
    @74
    @79
    @45
    ad2antrr
    @97
    erth
    mpbird
    @80
    @33
    @54
    @91
    @92
    wb
    wph
    @33
    @74
    @79
    @36
    ad2antrr
    #
    wph
    @54
    @74
    @79
    @55
    ad2antrr
    @7
    @83
    c.pl
    c.sm
    cK
    cG
    @81
    cgrp
    cX
    sylow2b.x
    @81
    eqid
    #
    sylow2b.a
    sylow2b.r
    eqgval
    syl2anc
    mpbid
    simp3d
    #
    vx
    @84
    @10
    @87
    cK
    @11
    @8
    @84
    wceq
    @9
    @86
    @7
    c.mi
    @8
    @84
    @7
    c.pl
    oveq2
    oveq1d
    @11
    eqid
    #
    @86
    @7
    c.mi
    ovex
    fvmpt
    syl
    @80
    @86
    @83
    @7
    c.mi
    @80
    @7
    @82
    c.pl
    co
    #
    @83
    c.pl
    co
    #
    @50
    @83
    c.pl
    co
    #
    @86
    @83
    @80
    @102
    @50
    @83
    c.pl
    @80
    @33
    @73
    @102
    @50
    wceq
    @98
    @97
    cX
    c.pl
    cG
    @81
    @7
    @50
    sylow2b.x
    sylow2b.a
    @52
    @99
    grprinv
    syl2anc
    oveq1d
    @80
    @33
    @73
    @82
    cX
    wcel
    #
    @90
    @103
    @86
    wceq
    @98
    @97
    @80
    @33
    @73
    @105
    @98
    @97
    cX
    cG
    @81
    @7
    sylow2b.x
    @99
    grpinvcl
    syl2anc
    @80
    @33
    @0
    cX
    wcel
    #
    @73
    @90
    @98
    @80
    cH
    cX
    @0
    wph
    @64
    @74
    @79
    @65
    ad2antrr
    @96
    sseldd
    #
    @97
    cX
    c.pl
    cG
    @0
    @7
    sylow2b.x
    sylow2b.a
    grpcl
    syl3anc
    #
    cX
    c.pl
    cG
    @7
    @82
    @83
    sylow2b.x
    sylow2b.a
    grpass
    syl13anc
    @80
    @33
    @90
    @104
    @83
    wceq
    @98
    @108
    cX
    c.pl
    cG
    @83
    @50
    sylow2b.x
    sylow2b.a
    @52
    grplid
    syl2anc
    3eqtr3d
    oveq1d
    @80
    @33
    @106
    @73
    @88
    @0
    wceq
    @98
    @107
    @97
    cX
    c.pl
    cG
    c.mi
    @0
    @7
    sylow2b.x
    sylow2b.a
    sylow2blem3.d
    grppncan
    syl3anc
    3eqtrd
    @80
    @11
    cK
    wfn
    @89
    @85
    @12
    wcel
    vx
    cK
    @10
    @11
    @9
    @7
    c.mi
    ovex
    @101
    fnmpti
    @100
    cK
    @84
    @11
    fnfvelrn
    sylancr
    eqeltrrd
    expr
    ralimdva
    imp
    an32s
    vu
    cH
    @12
    dfss3
    sylibr
    expr
    reximdva
    ex
    com23
    syl5bi
    rexlimdv
    mpd
end
