include "co.mm"
include "wbr.mm"
include "cv.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "wrex.mm"
include "copab.mm"
include "legval.mm"
include "breqd.mm"
include "ovex.mm"
include "simpr.mm"
include "eqeq1d.mm"
include "simpl.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "anbi12d.mm"
include "2rexbidv.mm"
include "eqid.mm"
include "braba.mm"
include "syl6bb.mm"
include "anass.mm"
include "anbi1i.mm"
include "cs3.mm"
include "ccgrg.mm"
include "cfv.mm"
include "cstrkg.mm"
include "ad5antr.mm"
include "adantr.mm"
include "simp-5r.mm"
include "simpllr.mm"
include "simp-4r.mm"
include "simprl.mm"
include "simprr.mm"
include "cgr3swap23.mm"
include "tgbtwnxfr.mm"
include "simplrr.mm"
include "cgr3simp1.mm"
include "eqtrd.mm"
include "jca.mm"
include "clng.mm"
include "simplr.mm"
include "btwncolg3.mm"
include "eqcomd.mm"
include "lnext.mm"
include "reximddv.mm"
include "adantllr.mm"
include "sylanbr.mm"
include "eleq1.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "sylibr.mm"
include "r19.29a.mm"
include "adantl3r.mm"
include "oveq1.mm"
include "eleq2d.mm"
include "anbi1d.mm"
include "cbvrex2v.mm"
include "r19.29vva.mm"
include "eqidd.mm"
include "rspc2ev.mm"
include "syl112anc.mm"
include "impbida.mm"
include "bitrd.mm"

theorem legov
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let c.le: class .<_
  let c.mi: class .-
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  assume legval.p: |- P = ( Base ` G )
  assume legval.d: |- .- = ( dist ` G )
  assume legval.i: |- I = ( Itv ` G )
  assume legval.l: |- .<_ = ( leG ` G )
  assume legval.g: |- ( ph -> G e. TarskiG )
  assume legov.a: |- ( ph -> A e. P )
  assume legov.b: |- ( ph -> B e. P )
  assume legov.c: |- ( ph -> C e. P )
  assume legov.d: |- ( ph -> D e. P )

  disjoint .- z
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint D z
  disjoint I z
  disjoint P z
  disjoint G z
  disjoint ph z
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint .- c
  disjoint d e
  disjoint d f
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint .- d
  disjoint e f
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint .- e
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint .- f
  disjoint x y
  disjoint x z
  disjoint .- x
  disjoint y z
  disjoint .- y
  disjoint A c
  disjoint A d
  disjoint A e
  disjoint A f
  disjoint A x
  disjoint A y
  disjoint B c
  disjoint B d
  disjoint B e
  disjoint B f
  disjoint B x
  disjoint B y
  disjoint C c
  disjoint C d
  disjoint C e
  disjoint C f
  disjoint C x
  disjoint C y
  disjoint D c
  disjoint D d
  disjoint D e
  disjoint D f
  disjoint D x
  disjoint D y
  disjoint I c
  disjoint I d
  disjoint I e
  disjoint I f
  disjoint I x
  disjoint I y
  disjoint P c
  disjoint P d
  disjoint P e
  disjoint P f
  disjoint P x
  disjoint P y
  disjoint G e
  disjoint G f
  disjoint G x
  disjoint G y
  disjoint c ph
  disjoint d ph
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( ( A .- B ) .<_ ( C .- D ) <-> E. z e. P ( z e. ( C I D ) /\ ( A .- B ) = ( C .- z ) ) ) )

  proof
    wph
    cA
    cB
    c.mi
    co
    #
    cC
    cD
    c.mi
    co
    #
    c.le
    wbr
    #
    @1
    vx
    cv
    #
    vy
    cv
    #
    c.mi
    co
    #
    wceq
    #
    vz
    cv
    #
    @3
    @4
    cI
    co
    #
    wcel
    #
    @0
    @3
    @7
    c.mi
    co
    #
    wceq
    #
    wa
    #
    vz
    cP
    wrex
    #
    wa
    #
    vy
    cP
    wrex
    vx
    cP
    wrex
    #
    @7
    cC
    cD
    cI
    co
    #
    wcel
    #
    @0
    cC
    @7
    c.mi
    co
    #
    wceq
    #
    wa
    #
    vz
    cP
    wrex
    #
    wph
    @2
    @0
    @1
    vf
    cv
    #
    @5
    wceq
    #
    @9
    ve
    cv
    #
    @10
    wceq
    #
    wa
    #
    vz
    cP
    wrex
    #
    wa
    #
    vy
    cP
    wrex
    vx
    cP
    wrex
    #
    ve
    vf
    copab
    #
    wbr
    @15
    wph
    c.le
    @30
    @0
    @1
    wph
    vx
    vy
    vz
    cP
    ve
    vf
    cG
    cI
    c.le
    c.mi
    legval.p
    legval.d
    legval.i
    legval.l
    legval.g
    legval
    breqd
    @29
    @15
    ve
    vf
    @0
    @1
    @30
    cA
    cB
    c.mi
    ovex
    cC
    cD
    c.mi
    ovex
    @24
    @0
    wceq
    #
    @22
    @1
    wceq
    #
    wa
    #
    @28
    @14
    vx
    vy
    cP
    cP
    @33
    @23
    @6
    @27
    @13
    @33
    @22
    @1
    @5
    @31
    @32
    simpr
    eqeq1d
    @33
    @26
    @12
    vz
    cP
    @33
    @25
    @11
    @9
    @33
    @24
    @0
    @10
    @31
    @32
    simpl
    eqeq1d
    anbi2d
    rexbidv
    anbi12d
    2rexbidv
    @30
    eqid
    braba
    syl6bb
    wph
    @15
    @21
    wph
    @15
    wa
    #
    @1
    vc
    cv
    #
    vd
    cv
    #
    c.mi
    co
    #
    wceq
    #
    @7
    @35
    @36
    cI
    co
    #
    wcel
    #
    @0
    @35
    @7
    c.mi
    co
    #
    wceq
    #
    wa
    #
    vz
    cP
    wrex
    #
    wa
    #
    @21
    vc
    vd
    cP
    cP
    wph
    @15
    @35
    cP
    wcel
    #
    @36
    cP
    wcel
    #
    @45
    @21
    wph
    @46
    wa
    #
    @47
    wa
    #
    @45
    wa
    #
    @3
    @39
    wcel
    #
    @0
    @35
    @3
    c.mi
    co
    #
    wceq
    #
    wa
    #
    @21
    vx
    cP
    @50
    @3
    cP
    wcel
    #
    wa
    @49
    @38
    wa
    #
    @44
    wa
    #
    @55
    wa
    @54
    @21
    @57
    @50
    @55
    @49
    @38
    @44
    anass
    anbi1i
    @56
    @55
    @54
    @21
    @44
    @56
    @55
    wa
    #
    @54
    wa
    #
    @35
    @36
    @3
    cs3
    cC
    cD
    @7
    cs3
    cG
    ccgrg
    cfv
    #
    wbr
    #
    @20
    vz
    cP
    @59
    @7
    cP
    wcel
    #
    @61
    wa
    #
    wa
    #
    @17
    @19
    @64
    @35
    @3
    @36
    cC
    cP
    @60
    @7
    cD
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    @60
    eqid
    #
    @59
    cG
    cstrkg
    wcel
    #
    @63
    wph
    @66
    @46
    @47
    @38
    @55
    @54
    legval.g
    ad5antr
    #
    adantr
    #
    @59
    @46
    @63
    wph
    @46
    @47
    @38
    @55
    @54
    simp-5r
    #
    adantr
    #
    @56
    @55
    @54
    @63
    simpllr
    #
    @59
    @47
    @63
    @48
    @47
    @38
    @55
    @54
    simp-4r
    #
    adantr
    #
    @59
    cC
    cP
    wcel
    #
    @63
    wph
    @74
    @46
    @47
    @38
    @55
    @54
    legov.c
    ad5antr
    #
    adantr
    #
    @59
    @62
    @61
    simprl
    #
    @59
    cD
    cP
    wcel
    #
    @63
    wph
    @78
    @46
    @47
    @38
    @55
    @54
    legov.d
    ad5antr
    #
    adantr
    #
    @64
    @35
    @36
    @3
    cC
    cP
    @60
    cD
    @7
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    @65
    @68
    @70
    @73
    @71
    @76
    @80
    @77
    @59
    @62
    @61
    simprr
    cgr3swap23
    #
    @59
    @51
    @63
    @58
    @51
    @53
    simprl
    #
    adantr
    tgbtwnxfr
    @64
    @0
    @52
    @18
    @58
    @51
    @53
    @63
    simplrr
    @64
    @35
    @3
    @36
    cC
    cP
    @60
    @7
    cD
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    @65
    @68
    @70
    @71
    @73
    @76
    @77
    @80
    @81
    cgr3simp1
    eqtrd
    jca
    @59
    cC
    cD
    cP
    @60
    cG
    cI
    cG
    clng
    cfv
    #
    c.mi
    @35
    @36
    @3
    vz
    legval.p
    @83
    eqid
    #
    legval.i
    @67
    @69
    @72
    @56
    @55
    @54
    simplr
    #
    @65
    @75
    @79
    legval.d
    @59
    cP
    cG
    cI
    @83
    @35
    @3
    @36
    legval.p
    @84
    legval.i
    @67
    @69
    @85
    @72
    @82
    btwncolg3
    @59
    @1
    @37
    @49
    @38
    @55
    @54
    simpllr
    eqcomd
    lnext
    reximddv
    adantllr
    sylanbr
    @50
    @44
    @54
    vx
    cP
    wrex
    @49
    @38
    @44
    simprr
    @54
    @43
    vx
    vz
    cP
    @3
    @7
    wceq
    #
    @51
    @40
    @53
    @42
    @3
    @7
    @39
    eleq1
    @86
    @52
    @41
    @0
    @3
    @7
    @35
    c.mi
    oveq2
    eqeq2d
    anbi12d
    cbvrexv
    sylibr
    r19.29a
    adantl3r
    @34
    @15
    @45
    vd
    cP
    wrex
    vc
    cP
    wrex
    wph
    @15
    simpr
    @45
    @14
    @1
    @3
    @36
    c.mi
    co
    #
    wceq
    #
    @7
    @3
    @36
    cI
    co
    #
    wcel
    #
    @11
    wa
    #
    vz
    cP
    wrex
    #
    wa
    vc
    vd
    vx
    vy
    cP
    cP
    @35
    @3
    wceq
    #
    @38
    @88
    @44
    @92
    @93
    @37
    @87
    @1
    @35
    @3
    @36
    c.mi
    oveq1
    eqeq2d
    @93
    @43
    @91
    vz
    cP
    @93
    @40
    @90
    @42
    @11
    @93
    @39
    @89
    @7
    @35
    @3
    @36
    cI
    oveq1
    eleq2d
    @93
    @41
    @10
    @0
    @35
    @3
    @7
    c.mi
    oveq1
    eqeq2d
    anbi12d
    rexbidv
    anbi12d
    @36
    @4
    wceq
    #
    @88
    @6
    @92
    @13
    @94
    @87
    @5
    @1
    @36
    @4
    @3
    c.mi
    oveq2
    eqeq2d
    @94
    @91
    @12
    vz
    cP
    @94
    @90
    @9
    @11
    @94
    @89
    @8
    @7
    @36
    @4
    @3
    cI
    oveq2
    eleq2d
    anbi1d
    rexbidv
    anbi12d
    cbvrex2v
    sylibr
    r19.29vva
    wph
    @21
    wa
    #
    @74
    @78
    @1
    @1
    wceq
    #
    @21
    @15
    wph
    @74
    @21
    legov.c
    adantr
    wph
    @78
    @21
    legov.d
    adantr
    @95
    @1
    eqidd
    wph
    @21
    simpr
    @14
    @96
    @21
    wa
    @1
    cC
    @4
    c.mi
    co
    #
    wceq
    #
    @7
    cC
    @4
    cI
    co
    #
    wcel
    #
    @19
    wa
    #
    vz
    cP
    wrex
    #
    wa
    vx
    vy
    cC
    cD
    cP
    cP
    @3
    cC
    wceq
    #
    @6
    @98
    @13
    @102
    @103
    @5
    @97
    @1
    @3
    cC
    @4
    c.mi
    oveq1
    eqeq2d
    @103
    @12
    @101
    vz
    cP
    @103
    @9
    @100
    @11
    @19
    @103
    @8
    @99
    @7
    @3
    cC
    @4
    cI
    oveq1
    eleq2d
    @103
    @10
    @18
    @0
    @3
    cC
    @7
    c.mi
    oveq1
    eqeq2d
    anbi12d
    rexbidv
    anbi12d
    @4
    cD
    wceq
    #
    @98
    @96
    @102
    @21
    @104
    @97
    @1
    @1
    @4
    cD
    cC
    c.mi
    oveq2
    eqeq2d
    @104
    @101
    @20
    vz
    cP
    @104
    @100
    @17
    @19
    @104
    @99
    @16
    @7
    @4
    cD
    cC
    cI
    oveq2
    eleq2d
    anbi1d
    rexbidv
    anbi12d
    rspc2ev
    syl112anc
    impbida
    bitrd
end
