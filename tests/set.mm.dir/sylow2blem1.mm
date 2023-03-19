include "wcel.mm"
include "w3a.mm"
include "cec.mm"
include "co.mm"
include "cv.mm"
include "cmpt.mm"
include "crn.mm"
include "cqs.mm"
include "wceq.mm"
include "simp2.mm"
include "cvv.mm"
include "cqg.mm"
include "ovex.mm"
include "eqeltri.mm"
include "simp3.mm"
include "ecelqsg.mm"
include "sylancr.mm"
include "wa.mm"
include "simpr.mm"
include "simpl.mm"
include "oveq1d.mm"
include "mpteq12dv.mm"
include "rneqd.mm"
include "ecexg.mm"
include "ax-mp.mm"
include "mptex.mm"
include "rnex.mm"
include "ovmpt2a.mm"
include "syl2anc.mm"
include "cfn.mm"
include "wss.mm"
include "cen.mm"
include "wbr.mm"
include "csubg.mm"
include "cfv.mm"
include "wer.mm"
include "eqger.mm"
include "syl.mm"
include "ecss.mm"
include "ssfi.mm"
include "3ad2ant1.mm"
include "wf.mm"
include "wb.mm"
include "vex.mm"
include "elecg.mm"
include "biimpa.mm"
include "cminusg.mm"
include "cgrp.mm"
include "subgrcl.mm"
include "subgss.mm"
include "sseldd.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "adantr.mm"
include "eqid.mm"
include "eqgval.mm"
include "simp2d.mm"
include "grpinvcl.mm"
include "grpass.mm"
include "syl13anc.mm"
include "csg.mm"
include "grpinvadd.mm"
include "grpsubval.mm"
include "eqtr4d.mm"
include "grpnpcan.mm"
include "eqtrd.mm"
include "eqtr3d.mm"
include "simp3d.mm"
include "eqeltrd.mm"
include "mpbir3and.mm"
include "elec.mm"
include "sylibr.mm"
include "syldan.mm"
include "fmptd.mm"
include "frn.mm"
include "wf1o.mm"
include "wf1.mm"
include "cres.mm"
include "grplmulf1o.mm"
include "f1of1.mm"
include "f1ssres.mm"
include "resmpt.mm"
include "f1eq1.mm"
include "3syl.mm"
include "mpbid.mm"
include "f1f1orn.mm"
include "f1oen.mm"
include "ensym.mm"
include "eqgen.mm"
include "entr.mm"
include "fisseneq.mm"

theorem sylow2blem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
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
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
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
  assert |- ( ( ph /\ B e. H /\ C e. X ) -> ( B .x. [ C ] .~ ) = [ ( B .+ C ) ] .~ )

  proof
    wph
    cB
    cH
    wcel
    #
    cC
    cX
    wcel
    #
    w3a
    #
    cB
    cC
    c.sm
    cec
    #
    c.x
    co
    #
    vz
    @3
    cB
    vz
    cv
    #
    c.pl
    co
    #
    cmpt
    #
    crn
    #
    cB
    cC
    c.pl
    co
    #
    c.sm
    cec
    #
    @2
    @0
    @3
    cX
    c.sm
    cqs
    #
    wcel
    #
    @4
    @8
    wceq
    wph
    @0
    @1
    simp2
    #
    @2
    c.sm
    cvv
    wcel
    #
    @1
    @12
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
    #
    wph
    @0
    @1
    simp3
    #
    cX
    cC
    c.sm
    cvv
    ecelqsg
    sylancr
    #
    vx
    vy
    cB
    @3
    cH
    @11
    vz
    vy
    cv
    #
    vx
    cv
    #
    @5
    c.pl
    co
    #
    cmpt
    #
    crn
    @8
    c.x
    @19
    cB
    wceq
    #
    @18
    @3
    wceq
    #
    wa
    #
    @21
    @7
    @24
    vz
    @18
    @20
    @3
    @6
    @22
    @23
    simpr
    @24
    @19
    cB
    @5
    c.pl
    @22
    @23
    simpl
    oveq1d
    mpteq12dv
    rneqd
    sylow2b.m
    @7
    vz
    @3
    @6
    @14
    @3
    cvv
    wcel
    @15
    cC
    cvv
    c.sm
    ecexg
    ax-mp
    #
    mptex
    rnex
    ovmpt2a
    syl2anc
    @2
    @10
    cfn
    wcel
    #
    @8
    @10
    wss
    #
    @8
    @10
    cen
    wbr
    #
    @8
    @10
    wceq
    wph
    @0
    @26
    @1
    wph
    cX
    cfn
    wcel
    @10
    cX
    wss
    @26
    sylow2b.xf
    wph
    @9
    c.sm
    cX
    wph
    cK
    cG
    csubg
    cfv
    #
    wcel
    #
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
    #
    ecss
    cX
    @10
    ssfi
    syl2anc
    3ad2ant1
    @2
    @3
    @10
    @7
    wf
    @27
    @2
    vz
    @3
    @6
    @10
    @7
    @2
    @5
    @3
    wcel
    #
    cC
    @5
    c.sm
    wbr
    #
    @6
    @10
    wcel
    #
    @2
    @32
    @33
    @2
    @5
    cvv
    wcel
    @1
    @32
    @33
    wb
    vz
    vex
    @16
    @5
    cC
    c.sm
    cvv
    cX
    elecg
    sylancr
    biimpa
    @2
    @33
    wa
    #
    @9
    @6
    c.sm
    wbr
    #
    @34
    @35
    @36
    @9
    cX
    wcel
    #
    @6
    cX
    wcel
    #
    @9
    cG
    cminusg
    cfv
    #
    cfv
    #
    @6
    c.pl
    co
    #
    cK
    wcel
    #
    @2
    @37
    @33
    @2
    cG
    cgrp
    wcel
    #
    cB
    cX
    wcel
    #
    @1
    @37
    wph
    @0
    @43
    @1
    wph
    cH
    @29
    wcel
    #
    @43
    sylow2b.h
    cH
    cG
    subgrcl
    syl
    #
    3ad2ant1
    #
    @2
    cH
    cX
    cB
    wph
    @0
    cH
    cX
    wss
    #
    @1
    wph
    @45
    @48
    sylow2b.h
    cX
    cH
    cG
    sylow2b.x
    subgss
    syl
    3ad2ant1
    @13
    sseldd
    #
    @16
    cX
    c.pl
    cG
    cB
    cC
    sylow2b.x
    sylow2b.a
    grpcl
    syl3anc
    #
    adantr
    @35
    @43
    @44
    @5
    cX
    wcel
    #
    @38
    @2
    @43
    @33
    @47
    adantr
    #
    @2
    @44
    @33
    @49
    adantr
    #
    @35
    @1
    @51
    cC
    @39
    cfv
    #
    @5
    c.pl
    co
    #
    cK
    wcel
    #
    @2
    @33
    @1
    @51
    @56
    w3a
    #
    wph
    @0
    @33
    @57
    wb
    #
    @1
    wph
    @43
    cK
    cX
    wss
    #
    @58
    @46
    wph
    @30
    @59
    sylow2b.k
    cX
    cK
    cG
    sylow2b.x
    subgss
    syl
    #
    cC
    @5
    c.pl
    c.sm
    cK
    cG
    @39
    cgrp
    cX
    sylow2b.x
    @39
    eqid
    #
    sylow2b.a
    sylow2b.r
    eqgval
    syl2anc
    3ad2ant1
    biimpa
    #
    simp2d
    #
    cX
    c.pl
    cG
    cB
    @5
    sylow2b.x
    sylow2b.a
    grpcl
    syl3anc
    @35
    @41
    @55
    cK
    @35
    @40
    cB
    c.pl
    co
    #
    @5
    c.pl
    co
    #
    @41
    @55
    @35
    @43
    @40
    cX
    wcel
    #
    @44
    @51
    @65
    @41
    wceq
    @52
    @2
    @66
    @33
    @2
    @43
    @37
    @66
    @47
    @50
    cX
    cG
    @39
    @9
    sylow2b.x
    @61
    grpinvcl
    syl2anc
    adantr
    @53
    @63
    cX
    c.pl
    cG
    @40
    cB
    @5
    sylow2b.x
    sylow2b.a
    grpass
    syl13anc
    @2
    @65
    @55
    wceq
    @33
    @2
    @64
    @54
    @5
    c.pl
    @2
    @64
    @54
    cB
    cG
    csg
    cfv
    #
    co
    #
    cB
    c.pl
    co
    #
    @54
    @2
    @40
    @68
    cB
    c.pl
    @2
    @40
    @54
    cB
    @39
    cfv
    c.pl
    co
    #
    @68
    @2
    @43
    @44
    @1
    @40
    @70
    wceq
    @47
    @49
    @16
    cX
    c.pl
    cG
    @39
    cB
    cC
    sylow2b.x
    sylow2b.a
    @61
    grpinvadd
    syl3anc
    @2
    @54
    cX
    wcel
    #
    @44
    @68
    @70
    wceq
    @2
    @43
    @1
    @71
    @47
    @16
    cX
    cG
    @39
    cC
    sylow2b.x
    @61
    grpinvcl
    syl2anc
    #
    @49
    cX
    c.pl
    cG
    @39
    @67
    @54
    cB
    sylow2b.x
    sylow2b.a
    @61
    @67
    eqid
    #
    grpsubval
    syl2anc
    eqtr4d
    oveq1d
    @2
    @43
    @71
    @44
    @69
    @54
    wceq
    @47
    @72
    @49
    cX
    c.pl
    cG
    @67
    @54
    cB
    sylow2b.x
    sylow2b.a
    @73
    grpnpcan
    syl3anc
    eqtrd
    oveq1d
    adantr
    eqtr3d
    @35
    @1
    @51
    @56
    @62
    simp3d
    eqeltrd
    @2
    @36
    @37
    @38
    @42
    w3a
    wb
    #
    @33
    wph
    @0
    @74
    @1
    wph
    @43
    @59
    @74
    @46
    @60
    @9
    @6
    c.pl
    c.sm
    cK
    cG
    @39
    cgrp
    cX
    sylow2b.x
    @61
    sylow2b.a
    sylow2b.r
    eqgval
    syl2anc
    3ad2ant1
    adantr
    mpbir3and
    @6
    @9
    c.sm
    cB
    @5
    c.pl
    ovex
    cB
    cC
    c.pl
    ovex
    elec
    sylibr
    syldan
    @7
    eqid
    fmptd
    @3
    @10
    @7
    frn
    syl
    @2
    @8
    @3
    cen
    wbr
    #
    @3
    @10
    cen
    wbr
    #
    @28
    @2
    @3
    @8
    @7
    wf1o
    #
    @3
    @8
    cen
    wbr
    @75
    @2
    @3
    cX
    @7
    wf1
    #
    @77
    @2
    @3
    cX
    vz
    cX
    @6
    cmpt
    #
    @3
    cres
    #
    wf1
    #
    @78
    @2
    cX
    cX
    @79
    wf1
    #
    @3
    cX
    wss
    #
    @81
    @2
    cX
    cX
    @79
    wf1o
    #
    @82
    @2
    @43
    @44
    @84
    @47
    @49
    vz
    cX
    c.pl
    @79
    cG
    cB
    sylow2b.x
    sylow2b.a
    @79
    eqid
    grplmulf1o
    syl2anc
    cX
    cX
    @79
    f1of1
    syl
    wph
    @0
    @83
    @1
    wph
    cC
    c.sm
    cX
    @31
    ecss
    3ad2ant1
    #
    cX
    cX
    @3
    @79
    f1ssres
    syl2anc
    @2
    @83
    @80
    @7
    wceq
    @81
    @78
    wb
    @85
    vz
    cX
    @3
    @6
    resmpt
    @3
    cX
    @80
    @7
    f1eq1
    3syl
    mpbid
    @3
    cX
    @7
    f1f1orn
    syl
    @3
    @8
    @7
    @25
    f1oen
    @3
    @8
    ensym
    3syl
    @2
    @3
    cK
    cen
    wbr
    #
    cK
    @10
    cen
    wbr
    #
    @76
    @2
    cK
    @3
    cen
    wbr
    #
    @86
    @2
    @30
    @12
    @88
    wph
    @0
    @30
    @1
    sylow2b.k
    3ad2ant1
    #
    @17
    @3
    c.sm
    cG
    cX
    cK
    sylow2b.x
    sylow2b.r
    eqgen
    syl2anc
    cK
    @3
    ensym
    syl
    @2
    @30
    @10
    @11
    wcel
    #
    @87
    @89
    @2
    @14
    @37
    @90
    @15
    @50
    cX
    @9
    c.sm
    cvv
    ecelqsg
    sylancr
    @10
    c.sm
    cG
    cX
    cK
    sylow2b.x
    sylow2b.r
    eqgen
    syl2anc
    @3
    cK
    @10
    entr
    syl2anc
    @8
    @3
    @10
    entr
    syl2anc
    @8
    @10
    fisseneq
    syl3anc
    eqtrd
end
