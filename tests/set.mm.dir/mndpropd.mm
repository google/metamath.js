include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "wcel.mm"
include "wral.mm"
include "cmnd.mm"
include "wa.mm"
include "cbs.mm"
include "simplr.mm"
include "simprl.mm"
include "wceq.mm"
include "ad2antrr.mm"
include "eleqtrd.mm"
include "simprr.mm"
include "eqid.mm"
include "mndcl.mm"
include "syl3anc.mm"
include "eleqtrrd.mm"
include "ralrimivva.mm"
include "ex.mm"
include "adantlr.mm"
include "3eltr4d.mm"
include "wb.mm"
include "wrex.mm"
include "oveqrspc2v.mm"
include "eleq1d.mm"
include "simplll.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simpllr.mm"
include "ovrspc2v.mm"
include "syl21anc.mm"
include "simpr.mm"
include "syl12anc.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "ralbidva.mm"
include "anbi12d.mm"
include "2ralbidva.mm"
include "adantr.mm"
include "eleq2d.mm"
include "raleqdv.mm"
include "raleqbidv.mm"
include "3bitr3d.mm"
include "eqeq1d.mm"
include "rexbidva.mm"
include "rexeqbidv.mm"
include "ismnd.mm"
include "3bitr4g.mm"
include "pm5.21ndd.mm"

theorem mndpropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cK: class K
  let cL: class L
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume mndpropd.1: |- ( ph -> B = ( Base ` K ) )
  assume mndpropd.2: |- ( ph -> B = ( Base ` L ) )
  assume mndpropd.3: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` K ) y ) = ( x ( +g ` L ) y ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint ph x
  disjoint ph y
  disjoint L x
  disjoint L y
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint B s
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint B u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint B v
  disjoint w x
  disjoint w y
  disjoint B w
  disjoint K s
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint ph s
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint L s
  disjoint L u
  disjoint L v
  disjoint L w
  assert |- ( ph -> ( K e. Mnd <-> L e. Mnd ) )

  proof
    wph
    vx
    cv
    #
    vy
    cv
    #
    cK
    cplusg
    cfv
    #
    co
    #
    cB
    wcel
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    cK
    cmnd
    wcel
    #
    cL
    cmnd
    wcel
    #
    wph
    @6
    @5
    wph
    @6
    wa
    #
    @4
    vx
    vy
    cB
    cB
    @8
    @0
    cB
    wcel
    #
    @1
    cB
    wcel
    #
    wa
    #
    wa
    #
    @3
    cK
    cbs
    cfv
    #
    cB
    @12
    @6
    @0
    @13
    wcel
    @1
    @13
    wcel
    @3
    @13
    wcel
    wph
    @6
    @11
    simplr
    @12
    @0
    cB
    @13
    @8
    @9
    @10
    simprl
    wph
    cB
    @13
    wceq
    #
    @6
    @11
    mndpropd.1
    ad2antrr
    #
    eleqtrd
    @12
    @1
    cB
    @13
    @8
    @9
    @10
    simprr
    @15
    eleqtrd
    @13
    @2
    cK
    @0
    @1
    @13
    eqid
    #
    @2
    eqid
    #
    mndcl
    syl3anc
    @15
    eleqtrrd
    ralrimivva
    ex
    wph
    @7
    @5
    wph
    @7
    wa
    #
    @4
    vx
    vy
    cB
    cB
    @18
    @11
    wa
    #
    @0
    @1
    cL
    cplusg
    cfv
    #
    co
    #
    cL
    cbs
    cfv
    #
    @3
    cB
    @19
    @7
    @0
    @22
    wcel
    @1
    @22
    wcel
    @21
    @22
    wcel
    wph
    @7
    @11
    simplr
    @19
    @0
    cB
    @22
    @18
    @9
    @10
    simprl
    wph
    cB
    @22
    wceq
    #
    @7
    @11
    mndpropd.2
    ad2antrr
    #
    eleqtrd
    @19
    @1
    cB
    @22
    @18
    @9
    @10
    simprr
    @24
    eleqtrd
    @22
    @20
    cL
    @0
    @1
    @22
    eqid
    #
    @20
    eqid
    #
    mndcl
    syl3anc
    wph
    @11
    @3
    @21
    wceq
    @7
    mndpropd.3
    adantlr
    @24
    3eltr4d
    ralrimivva
    ex
    wph
    @5
    @6
    @7
    wb
    wph
    @5
    wa
    #
    vu
    cv
    #
    vv
    cv
    #
    @2
    co
    #
    @13
    wcel
    #
    @30
    vw
    cv
    #
    @2
    co
    #
    @28
    @29
    @32
    @2
    co
    #
    @2
    co
    #
    wceq
    #
    vw
    @13
    wral
    #
    wa
    #
    vv
    @13
    wral
    #
    vu
    @13
    wral
    #
    vs
    cv
    #
    @28
    @2
    co
    #
    @28
    wceq
    #
    @28
    @41
    @2
    co
    #
    @28
    wceq
    #
    wa
    #
    vu
    @13
    wral
    #
    vs
    @13
    wrex
    #
    wa
    @28
    @29
    @20
    co
    #
    @22
    wcel
    #
    @49
    @32
    @20
    co
    #
    @28
    @29
    @32
    @20
    co
    #
    @20
    co
    #
    wceq
    #
    vw
    @22
    wral
    #
    wa
    #
    vv
    @22
    wral
    #
    vu
    @22
    wral
    #
    @41
    @28
    @20
    co
    #
    @28
    wceq
    #
    @28
    @41
    @20
    co
    #
    @28
    wceq
    #
    wa
    #
    vu
    @22
    wral
    #
    vs
    @22
    wrex
    #
    wa
    @6
    @7
    @27
    @40
    @58
    @48
    @65
    @27
    @30
    cB
    wcel
    #
    @36
    vw
    cB
    wral
    #
    wa
    #
    vv
    cB
    wral
    #
    vu
    cB
    wral
    @49
    cB
    wcel
    #
    @54
    vw
    cB
    wral
    #
    wa
    #
    vv
    cB
    wral
    #
    vu
    cB
    wral
    @40
    @58
    @27
    @68
    @72
    vu
    vv
    cB
    cB
    @27
    @28
    cB
    wcel
    #
    @29
    cB
    wcel
    #
    wa
    #
    wa
    #
    @66
    @70
    @67
    @71
    @77
    @30
    @49
    cB
    wph
    @76
    @30
    @49
    wceq
    #
    @5
    wph
    vx
    vy
    cB
    cB
    @2
    @20
    @28
    @29
    mndpropd.3
    oveqrspc2v
    #
    adantlr
    eleq1d
    @77
    @36
    @54
    vw
    cB
    @77
    @32
    cB
    wcel
    #
    wa
    #
    @33
    @51
    @35
    @53
    @81
    @33
    @30
    @32
    @20
    co
    #
    @51
    @81
    wph
    @66
    @80
    @33
    @82
    wceq
    wph
    @5
    @76
    @80
    simplll
    #
    @81
    @74
    @75
    @5
    @66
    @27
    @74
    @75
    @80
    simplrl
    #
    @27
    @74
    @75
    @80
    simplrr
    #
    wph
    @5
    @76
    @80
    simpllr
    #
    vx
    vy
    cB
    cB
    cB
    @2
    @28
    @29
    ovrspc2v
    syl21anc
    @77
    @80
    simpr
    #
    wph
    vx
    vy
    cB
    cB
    @2
    @20
    @30
    @32
    mndpropd.3
    oveqrspc2v
    syl12anc
    @81
    @30
    @49
    @32
    @20
    @81
    wph
    @74
    @75
    @78
    @83
    @84
    @85
    @79
    syl12anc
    oveq1d
    eqtrd
    @81
    @35
    @28
    @34
    @20
    co
    #
    @53
    @81
    wph
    @74
    @34
    cB
    wcel
    #
    @35
    @88
    wceq
    @83
    @84
    @81
    @75
    @80
    @5
    @89
    @85
    @87
    @86
    vx
    vy
    cB
    cB
    cB
    @2
    @29
    @32
    ovrspc2v
    syl21anc
    wph
    vx
    vy
    cB
    cB
    @2
    @20
    @28
    @34
    mndpropd.3
    oveqrspc2v
    syl12anc
    @81
    @34
    @52
    @28
    @20
    @81
    wph
    @75
    @80
    @34
    @52
    wceq
    @83
    @85
    @87
    wph
    vx
    vy
    cB
    cB
    @2
    @20
    @29
    @32
    mndpropd.3
    oveqrspc2v
    syl12anc
    oveq2d
    eqtrd
    eqeq12d
    ralbidva
    anbi12d
    2ralbidva
    @27
    @69
    @39
    vu
    cB
    @13
    wph
    @14
    @5
    mndpropd.1
    adantr
    #
    @27
    @68
    @38
    vv
    cB
    @13
    @90
    @27
    @66
    @31
    @67
    @37
    @27
    cB
    @13
    @30
    @90
    eleq2d
    @27
    @36
    vw
    cB
    @13
    @90
    raleqdv
    anbi12d
    raleqbidv
    raleqbidv
    @27
    @73
    @57
    vu
    cB
    @22
    wph
    @23
    @5
    mndpropd.2
    adantr
    #
    @27
    @72
    @56
    vv
    cB
    @22
    @91
    @27
    @70
    @50
    @71
    @55
    @27
    cB
    @22
    @49
    @91
    eleq2d
    @27
    @54
    vw
    cB
    @22
    @91
    raleqdv
    anbi12d
    raleqbidv
    raleqbidv
    3bitr3d
    @27
    @46
    vu
    cB
    wral
    #
    vs
    cB
    wrex
    @63
    vu
    cB
    wral
    #
    vs
    cB
    wrex
    @48
    @65
    @27
    @92
    @93
    vs
    cB
    @27
    @41
    cB
    wcel
    #
    wa
    #
    @46
    @63
    vu
    cB
    @95
    @74
    wa
    #
    @43
    @60
    @45
    @62
    @96
    @42
    @59
    @28
    @96
    wph
    @94
    @74
    @42
    @59
    wceq
    wph
    @5
    @94
    @74
    simplll
    #
    @27
    @94
    @74
    simplr
    #
    @95
    @74
    simpr
    #
    wph
    vx
    vy
    cB
    cB
    @2
    @20
    @41
    @28
    mndpropd.3
    oveqrspc2v
    syl12anc
    eqeq1d
    @96
    @44
    @61
    @28
    @96
    wph
    @74
    @94
    @44
    @61
    wceq
    @97
    @99
    @98
    wph
    vx
    vy
    cB
    cB
    @2
    @20
    @28
    @41
    mndpropd.3
    oveqrspc2v
    syl12anc
    eqeq1d
    anbi12d
    ralbidva
    rexbidva
    @27
    @92
    @47
    vs
    cB
    @13
    @90
    @27
    @46
    vu
    cB
    @13
    @90
    raleqdv
    rexeqbidv
    @27
    @93
    @64
    vs
    cB
    @22
    @91
    @27
    @63
    vu
    cB
    @22
    @91
    raleqdv
    rexeqbidv
    3bitr3d
    anbi12d
    @13
    @2
    vs
    cK
    vu
    vv
    vw
    @16
    @17
    ismnd
    @22
    @20
    vs
    cL
    vu
    vv
    vw
    @25
    @26
    ismnd
    3bitr4g
    ex
    pm5.21ndd
end
