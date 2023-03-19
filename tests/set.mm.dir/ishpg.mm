include "chpg.mm"
include "cfv.mm"
include "cv.mm"
include "cdif.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wrex.mm"
include "copab.mm"
include "wbr.mm"
include "crn.mm"
include "cvv.mm"
include "cstrkg.mm"
include "cmpt.mm"
include "wceq.mm"
include "elex.mm"
include "clng.mm"
include "citv.mm"
include "wsbc.mm"
include "cbs.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "rneqd.mm"
include "simpl.mm"
include "eqcomd.mm"
include "difeq1d.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "simpr.mm"
include "oveqd.mm"
include "rexbidv.mm"
include "rexeqbidv.mm"
include "sbcie2s.mm"
include "opabbidv.mm"
include "mpteq12dv.mm"
include "df-hpg.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rnex.mm"
include "mptex.mm"
include "fvmpt.mm"
include "3syl.mm"
include "difeq2.mm"
include "id.mm"
include "rexeqdv.mm"
include "adantl.mm"
include "cxp.mm"
include "df-xp.mm"
include "xpex.mm"
include "eqeltrri.mm"
include "eldifi.mm"
include "anim12i.mm"
include "adantrr.mm"
include "adantlr.mm"
include "rexlimivw.mm"
include "ssopab2i.mm"
include "ssexi.mm"
include "a1i.mm"
include "fvmptd.mm"
include "vex.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "oveq1.mm"
include "anbi2d.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "oveq12.mm"
include "cbvopabv.mm"
include "eqtri.mm"
include "brab.mm"
include "anbi12i.mm"
include "rexbii.mm"
include "opabbii.mm"
include "eqtr4d.mm"

theorem ishpg
  let wph: wff ph
  let vt: setvar t
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let cO: class O
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vp: setvar p
  assume ishpg.p: |- P = ( Base ` G )
  assume ishpg.i: |- I = ( Itv ` G )
  assume ishpg.l: |- L = ( LineG ` G )
  assume ishpg.o: |- O = { <. a , b >. | ( ( a e. ( P \ D ) /\ b e. ( P \ D ) ) /\ E. t e. D t e. ( a I b ) ) }
  assume ishpg.g: |- ( ph -> G e. TarskiG )
  assume ishpg.d: |- ( ph -> D e. ran L )

  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D t
  disjoint a b
  disjoint a c
  disjoint a t
  disjoint b c
  disjoint b t
  disjoint c t
  disjoint G a
  disjoint G b
  disjoint I a
  disjoint I b
  disjoint I c
  disjoint I t
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P t
  disjoint D d
  disjoint a d
  disjoint b d
  disjoint c d
  disjoint d t
  disjoint D e
  disjoint D f
  disjoint a e
  disjoint a f
  disjoint b e
  disjoint b f
  disjoint c e
  disjoint c f
  disjoint e f
  disjoint e t
  disjoint f t
  disjoint G d
  disjoint G g
  disjoint G i
  disjoint G p
  disjoint a g
  disjoint a i
  disjoint a p
  disjoint b g
  disjoint b i
  disjoint b p
  disjoint d g
  disjoint d i
  disjoint d p
  disjoint g i
  disjoint g p
  disjoint i p
  disjoint d ph
  disjoint I d
  disjoint I e
  disjoint I f
  disjoint I g
  disjoint I i
  disjoint I p
  disjoint c g
  disjoint c i
  disjoint c p
  disjoint d e
  disjoint d f
  disjoint e g
  disjoint e i
  disjoint e p
  disjoint f g
  disjoint f i
  disjoint f p
  disjoint g t
  disjoint i t
  disjoint p t
  disjoint L d
  disjoint L g
  disjoint P d
  disjoint P e
  disjoint P f
  disjoint P g
  disjoint P i
  disjoint P p
  assert |- ( ph -> ( ( hpG ` G ) ` D ) = { <. a , b >. | E. c e. P ( a O c /\ b O c ) } )

  proof
    wph
    cD
    cG
    chpg
    cfv
    #
    cfv
    va
    cv
    #
    cP
    cD
    cdif
    #
    wcel
    #
    vc
    cv
    #
    @2
    wcel
    #
    wa
    #
    vt
    cv
    #
    @1
    @4
    cI
    co
    #
    wcel
    #
    vt
    cD
    wrex
    #
    wa
    #
    vb
    cv
    #
    @2
    wcel
    #
    @5
    wa
    #
    @7
    @12
    @4
    cI
    co
    #
    wcel
    #
    vt
    cD
    wrex
    #
    wa
    #
    wa
    #
    vc
    cP
    wrex
    #
    va
    vb
    copab
    #
    @1
    @4
    cO
    wbr
    #
    @12
    @4
    cO
    wbr
    #
    wa
    #
    vc
    cP
    wrex
    #
    va
    vb
    copab
    #
    wph
    vd
    cD
    @1
    cP
    vd
    cv
    #
    cdif
    #
    wcel
    #
    @4
    @28
    wcel
    #
    wa
    #
    @9
    vt
    @27
    wrex
    #
    wa
    #
    @12
    @28
    wcel
    #
    @30
    wa
    #
    @16
    vt
    @27
    wrex
    #
    wa
    #
    wa
    #
    vc
    cP
    wrex
    #
    va
    vb
    copab
    #
    @21
    cL
    crn
    #
    @0
    cvv
    wph
    cG
    cstrkg
    wcel
    cG
    cvv
    wcel
    @0
    vd
    @41
    @40
    cmpt
    #
    wceq
    ishpg.g
    cG
    cstrkg
    elex
    vg
    cG
    vd
    vg
    cv
    #
    clng
    cfv
    #
    crn
    #
    @1
    vp
    cv
    #
    @27
    cdif
    #
    wcel
    #
    @4
    @47
    wcel
    #
    wa
    #
    @7
    @1
    @4
    vi
    cv
    #
    co
    #
    wcel
    #
    vt
    @27
    wrex
    #
    wa
    #
    @12
    @47
    wcel
    #
    @49
    wa
    #
    @7
    @12
    @4
    @51
    co
    #
    wcel
    #
    vt
    @27
    wrex
    #
    wa
    #
    wa
    #
    vc
    @46
    wrex
    #
    vi
    @43
    citv
    cfv
    wsbc
    vp
    @43
    cbs
    cfv
    wsbc
    #
    va
    vb
    copab
    #
    cmpt
    @42
    cvv
    chpg
    @43
    cG
    wceq
    #
    vd
    @45
    @65
    @41
    @40
    @66
    @44
    cL
    @66
    @44
    cG
    clng
    cfv
    #
    cL
    @43
    cG
    clng
    fveq2
    ishpg.l
    syl6eqr
    rneqd
    @66
    @64
    @39
    va
    vb
    @39
    @63
    vg
    cP
    cI
    cbs
    citv
    cG
    vp
    vi
    ishpg.p
    ishpg.i
    @46
    cP
    wceq
    #
    @51
    cI
    wceq
    #
    wa
    #
    @38
    @62
    vc
    cP
    @46
    @70
    @46
    cP
    @68
    @69
    simpl
    eqcomd
    #
    @70
    @33
    @55
    @37
    @61
    @70
    @31
    @50
    @32
    @54
    @70
    @29
    @48
    @30
    @49
    @70
    @28
    @47
    @1
    @70
    cP
    @46
    @27
    @71
    difeq1d
    #
    eleq2d
    @70
    @28
    @47
    @4
    @72
    eleq2d
    #
    anbi12d
    @70
    @9
    @53
    vt
    @27
    @70
    @8
    @52
    @7
    @70
    cI
    @51
    @1
    @4
    @70
    @51
    cI
    @68
    @69
    simpr
    eqcomd
    #
    oveqd
    eleq2d
    rexbidv
    anbi12d
    @70
    @35
    @57
    @36
    @60
    @70
    @34
    @56
    @30
    @49
    @70
    @28
    @47
    @12
    @72
    eleq2d
    @73
    anbi12d
    @70
    @16
    @59
    vt
    @27
    @70
    @15
    @58
    @7
    @70
    cI
    @51
    @12
    @4
    @74
    oveqd
    eleq2d
    rexbidv
    anbi12d
    anbi12d
    rexeqbidv
    sbcie2s
    opabbidv
    mpteq12dv
    vt
    vg
    vi
    vp
    va
    vb
    vc
    vd
    df-hpg
    vd
    @41
    @40
    cL
    cL
    @67
    cvv
    ishpg.l
    cG
    clng
    fvex
    eqeltri
    rnex
    mptex
    fvmpt
    3syl
    @27
    cD
    wceq
    #
    @40
    @21
    wceq
    wph
    @75
    @39
    @20
    va
    vb
    @75
    @38
    @19
    vc
    cP
    @75
    @33
    @11
    @37
    @18
    @75
    @31
    @6
    @32
    @10
    @75
    @29
    @3
    @30
    @5
    @75
    @28
    @2
    @1
    @27
    cD
    cP
    difeq2
    #
    eleq2d
    @75
    @28
    @2
    @4
    @76
    eleq2d
    #
    anbi12d
    @75
    @9
    vt
    @27
    cD
    @75
    id
    #
    rexeqdv
    anbi12d
    @75
    @35
    @14
    @36
    @17
    @75
    @34
    @13
    @30
    @5
    @75
    @28
    @2
    @12
    @76
    eleq2d
    @77
    anbi12d
    @75
    @16
    vt
    @27
    cD
    @78
    rexeqdv
    anbi12d
    anbi12d
    rexbidv
    opabbidv
    adantl
    ishpg.d
    @21
    cvv
    wcel
    wph
    @21
    @1
    cP
    wcel
    #
    @12
    cP
    wcel
    #
    wa
    #
    va
    vb
    copab
    #
    cP
    cP
    cxp
    @82
    cvv
    va
    vb
    cP
    cP
    df-xp
    cP
    cP
    cP
    cG
    cbs
    cfv
    cvv
    ishpg.p
    cG
    cbs
    fvex
    eqeltri
    #
    @83
    xpex
    eqeltrri
    @20
    @81
    va
    vb
    @19
    @81
    vc
    cP
    @11
    @14
    @81
    @17
    @6
    @14
    @81
    @10
    @3
    @14
    @81
    @5
    @3
    @13
    @81
    @5
    @3
    @79
    @13
    @80
    @1
    cP
    cD
    eldifi
    @12
    cP
    cD
    eldifi
    anim12i
    adantrr
    adantlr
    adantlr
    adantrr
    rexlimivw
    ssopab2i
    ssexi
    a1i
    fvmptd
    @26
    @21
    wceq
    wph
    @25
    @20
    va
    vb
    @24
    @19
    vc
    cP
    @22
    @11
    @23
    @18
    ve
    cv
    #
    @2
    wcel
    #
    vf
    cv
    #
    @2
    wcel
    #
    wa
    #
    @7
    @84
    @86
    cI
    co
    #
    wcel
    #
    vt
    cD
    wrex
    #
    wa
    #
    @3
    @87
    wa
    #
    @7
    @1
    @86
    cI
    co
    #
    wcel
    #
    vt
    cD
    wrex
    #
    wa
    @11
    ve
    vf
    @1
    @4
    cO
    va
    vex
    vc
    vex
    #
    @84
    @1
    wceq
    #
    @88
    @93
    @91
    @96
    @98
    @85
    @3
    @87
    @84
    @1
    @2
    eleq1
    anbi1d
    @98
    @90
    @95
    vt
    cD
    @98
    @89
    @94
    @7
    @84
    @1
    @86
    cI
    oveq1
    eleq2d
    rexbidv
    anbi12d
    @86
    @4
    wceq
    #
    @93
    @6
    @96
    @10
    @99
    @87
    @5
    @3
    @86
    @4
    @2
    eleq1
    #
    anbi2d
    @99
    @95
    @9
    vt
    cD
    @99
    @94
    @8
    @7
    @86
    @4
    @1
    cI
    oveq2
    eleq2d
    rexbidv
    anbi12d
    cO
    @3
    @13
    wa
    #
    @7
    @1
    @12
    cI
    co
    #
    wcel
    #
    vt
    cD
    wrex
    #
    wa
    #
    va
    vb
    copab
    @92
    ve
    vf
    copab
    ishpg.o
    @105
    @92
    va
    vb
    ve
    vf
    @1
    @84
    wceq
    #
    @12
    @86
    wceq
    #
    wa
    #
    @101
    @88
    @104
    @91
    @108
    @3
    @85
    @13
    @87
    @108
    @1
    @84
    @2
    @106
    @107
    simpl
    eleq1d
    @108
    @12
    @86
    @2
    @106
    @107
    simpr
    eleq1d
    anbi12d
    @108
    @103
    @90
    vt
    cD
    @108
    @102
    @89
    @7
    @1
    @84
    @12
    @86
    cI
    oveq12
    eleq2d
    rexbidv
    anbi12d
    cbvopabv
    eqtri
    #
    brab
    @92
    @13
    @87
    wa
    #
    @7
    @12
    @86
    cI
    co
    #
    wcel
    #
    vt
    cD
    wrex
    #
    wa
    @18
    ve
    vf
    @12
    @4
    cO
    vb
    vex
    @97
    @84
    @12
    wceq
    #
    @88
    @110
    @91
    @113
    @114
    @85
    @13
    @87
    @84
    @12
    @2
    eleq1
    anbi1d
    @114
    @90
    @112
    vt
    cD
    @114
    @89
    @111
    @7
    @84
    @12
    @86
    cI
    oveq1
    eleq2d
    rexbidv
    anbi12d
    @99
    @110
    @14
    @113
    @17
    @99
    @87
    @5
    @13
    @100
    anbi2d
    @99
    @112
    @16
    vt
    cD
    @99
    @111
    @15
    @7
    @86
    @4
    @12
    cI
    oveq2
    eleq2d
    rexbidv
    anbi12d
    @109
    brab
    anbi12i
    rexbii
    opabbii
    a1i
    eqtr4d
end
