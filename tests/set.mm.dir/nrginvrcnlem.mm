include "crp.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "c1.mm"
include "cmul.mm"
include "cle.mm"
include "cif.mm"
include "c2.mm"
include "cdiv.mm"
include "1rp.mm"
include "cngp.mm"
include "c0g.mm"
include "wne.mm"
include "cnrg.mm"
include "nrgngp.mm"
include "syl.mm"
include "unitss.mm"
include "sseldi.mm"
include "cnzr.mm"
include "eqid.mm"
include "nzrunit.mm"
include "syl2anc.mm"
include "nmrpcl.mm"
include "syl3anc.mm"
include "rpmulcld.mm"
include "ifcl.mm"
include "sylancr.mm"
include "rphalfcld.mm"
include "syl5eqel.mm"
include "wa.mm"
include "csg.mm"
include "wceq.mm"
include "cur.mm"
include "cmulr.mm"
include "cr.mm"
include "adantr.mm"
include "unitcl.mm"
include "nmcl.mm"
include "recnd.mm"
include "simprl.mm"
include "cgrp.mm"
include "ngpgrp.mm"
include "crg.mm"
include "nrgring.mm"
include "ringinvcl.mm"
include "grpsubcl.mm"
include "mul32d.mm"
include "nmmul.mm"
include "ringsubdi.mm"
include "unitrinv.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "ringidcl.mm"
include "ringcl.mm"
include "rngsubdir.mm"
include "ringlidm.mm"
include "ringass.mm"
include "syl13anc.mm"
include "unitlinv.mm"
include "oveq2d.mm"
include "ringridm.mm"
include "3eqtrd.mm"
include "oveq12d.mm"
include "rpred.mm"
include "rpne0d.mm"
include "divmuld.mm"
include "mpbird.mm"
include "ngpdsr.mm"
include "ngpds.mm"
include "3eqtr4rd.mm"
include "eqeltrd.mm"
include "remulcld.mm"
include "simprr.mm"
include "1re.mm"
include "min2.mm"
include "lemul1d.mm"
include "mpbid.mm"
include "syl5eqbr.mm"
include "caddc.mm"
include "2halvesd.mm"
include "cmin.mm"
include "resubcld.mm"
include "nm2dif.mm"
include "breqtrrd.mm"
include "min1.mm"
include "1red.mm"
include "mulid2d.mm"
include "breqtrd.mm"
include "ltletrd.mm"
include "lelttrd.mm"
include "ltsubadd2d.mm"
include "eqbrtrd.mm"
include "ltadd1d.mm"
include "ltmul2dd.mm"
include "lttrd.mm"
include "ltdivmuld.mm"
include "expr.mm"
include "ralrimiva.mm"
include "breq2.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"

theorem nrginvrcnlem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cT: class T
  let cU: class U
  let cI: class I
  let cN: class N
  let cX: class X
  let vr: setvar r
  let vs: setvar s
  assume nrginvrcn.x: |- X = ( Base ` R )
  assume nrginvrcn.u: |- U = ( Unit ` R )
  assume nrginvrcn.i: |- I = ( invr ` R )
  assume nrginvrcn.n: |- N = ( norm ` R )
  assume nrginvrcn.d: |- D = ( dist ` R )
  assume nrginvrcn.r: |- ( ph -> R e. NrmRing )
  assume nrginvrcn.z: |- ( ph -> R e. NzRing )
  assume nrginvrcn.a: |- ( ph -> A e. U )
  assume nrginvrcn.b: |- ( ph -> B e. RR+ )
  assume nrginvrcn.t: |- T = ( if ( 1 <_ ( ( N ` A ) x. B ) , 1 , ( ( N ` A ) x. B ) ) x. ( ( N ` A ) / 2 ) )

  disjoint x y
  disjoint I x
  disjoint I y
  disjoint ph y
  disjoint R x
  disjoint R y
  disjoint T x
  disjoint T y
  disjoint U x
  disjoint U y
  disjoint A x
  disjoint B x
  disjoint D x
  disjoint r s
  disjoint r x
  disjoint r y
  disjoint I r
  disjoint s x
  disjoint s y
  disjoint I s
  disjoint R r
  disjoint R s
  disjoint U r
  disjoint U s
  assert |- ( ph -> E. x e. RR+ A. y e. U ( ( A D y ) < x -> ( ( I ` A ) D ( I ` y ) ) < B ) )

  proof
    wph
    cT
    crp
    wcel
    #
    cA
    vy
    cv
    #
    cD
    co
    #
    cT
    clt
    wbr
    #
    cA
    cI
    cfv
    #
    @1
    cI
    cfv
    #
    cD
    co
    #
    cB
    clt
    wbr
    #
    wi
    #
    vy
    cU
    wral
    #
    @2
    vx
    cv
    #
    clt
    wbr
    #
    @7
    wi
    #
    vy
    cU
    wral
    #
    vx
    crp
    wrex
    wph
    cT
    c1
    cA
    cN
    cfv
    #
    cB
    cmul
    co
    #
    cle
    wbr
    #
    c1
    @15
    cif
    #
    @14
    c2
    cdiv
    co
    #
    cmul
    co
    #
    crp
    nrginvrcn.t
    wph
    @17
    @18
    wph
    c1
    crp
    wcel
    @15
    crp
    wcel
    #
    @17
    crp
    wcel
    #
    1rp
    wph
    @14
    cB
    wph
    cR
    cngp
    wcel
    #
    cA
    cX
    wcel
    #
    cA
    cR
    c0g
    cfv
    #
    wne
    #
    @14
    crp
    wcel
    #
    wph
    cR
    cnrg
    wcel
    #
    @22
    nrginvrcn.r
    cR
    nrgngp
    syl
    #
    wph
    cU
    cX
    cA
    cX
    cR
    cU
    nrginvrcn.x
    nrginvrcn.u
    unitss
    #
    nrginvrcn.a
    sseldi
    wph
    cR
    cnzr
    wcel
    #
    cA
    cU
    wcel
    #
    @25
    nrginvrcn.z
    nrginvrcn.a
    cA
    cR
    cU
    @24
    nrginvrcn.u
    @24
    eqid
    #
    nzrunit
    syl2anc
    cA
    cR
    cN
    cX
    @24
    nrginvrcn.x
    nrginvrcn.n
    @32
    nmrpcl
    syl3anc
    #
    nrginvrcn.b
    rpmulcld
    #
    @16
    c1
    @15
    crp
    ifcl
    sylancr
    #
    wph
    @14
    @33
    rphalfcld
    rpmulcld
    syl5eqel
    #
    wph
    @8
    vy
    cU
    wph
    @1
    cU
    wcel
    #
    @3
    @7
    wph
    @37
    @3
    wa
    #
    wa
    #
    @6
    @2
    @14
    @1
    cN
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    cB
    clt
    @39
    @1
    cA
    cR
    csg
    cfv
    #
    co
    #
    cN
    cfv
    #
    @41
    cdiv
    co
    #
    @4
    @5
    @43
    co
    #
    cN
    cfv
    #
    @42
    @6
    @39
    @46
    @48
    wceq
    @41
    @48
    cmul
    co
    #
    @45
    wceq
    @39
    @49
    @14
    @48
    cmul
    co
    #
    @40
    cmul
    co
    cR
    cur
    cfv
    #
    cA
    @5
    cR
    cmulr
    cfv
    #
    co
    #
    @43
    co
    #
    cN
    cfv
    #
    @40
    cmul
    co
    #
    @45
    @39
    @14
    @40
    @48
    @39
    @14
    @39
    @22
    @23
    @14
    cr
    wcel
    wph
    @22
    @38
    @28
    adantr
    #
    @39
    @31
    @23
    wph
    @31
    @38
    nrginvrcn.a
    adantr
    #
    cX
    cR
    cU
    cA
    nrginvrcn.x
    nrginvrcn.u
    unitcl
    syl
    #
    cA
    cR
    cN
    cX
    nrginvrcn.x
    nrginvrcn.n
    nmcl
    syl2anc
    #
    recnd
    #
    @39
    @40
    @39
    @22
    @1
    cX
    wcel
    #
    @40
    cr
    wcel
    @57
    @39
    cU
    cX
    @1
    @29
    wph
    @37
    @3
    simprl
    #
    sseldi
    #
    @1
    cR
    cN
    cX
    nrginvrcn.x
    nrginvrcn.n
    nmcl
    syl2anc
    #
    recnd
    #
    @39
    @48
    @39
    @22
    @47
    cX
    wcel
    #
    @48
    cr
    wcel
    @57
    @39
    cR
    cgrp
    wcel
    #
    @4
    cX
    wcel
    #
    @5
    cX
    wcel
    #
    @67
    @39
    @22
    @68
    @57
    cR
    ngpgrp
    syl
    #
    @39
    cR
    crg
    wcel
    #
    @31
    @69
    wph
    @72
    @38
    wph
    @27
    @72
    nrginvrcn.r
    cR
    nrgring
    syl
    adantr
    #
    @58
    cX
    cR
    cU
    cI
    cA
    nrginvrcn.u
    nrginvrcn.i
    nrginvrcn.x
    ringinvcl
    syl2anc
    #
    @39
    @72
    @37
    @70
    @73
    @63
    cX
    cR
    cU
    cI
    @1
    nrginvrcn.u
    nrginvrcn.i
    nrginvrcn.x
    ringinvcl
    syl2anc
    #
    cX
    cR
    @43
    @4
    @5
    nrginvrcn.x
    @43
    eqid
    #
    grpsubcl
    syl3anc
    #
    @47
    cR
    cN
    cX
    nrginvrcn.x
    nrginvrcn.n
    nmcl
    syl2anc
    recnd
    #
    mul32d
    @39
    @50
    @55
    @40
    cmul
    @39
    cA
    @47
    @52
    co
    #
    cN
    cfv
    #
    @50
    @55
    @39
    @27
    @23
    @67
    @80
    @50
    wceq
    wph
    @27
    @38
    nrginvrcn.r
    adantr
    #
    @59
    @77
    cA
    @47
    cR
    @52
    cN
    cX
    nrginvrcn.x
    nrginvrcn.n
    @52
    eqid
    #
    nmmul
    syl3anc
    @39
    @79
    @54
    cN
    @39
    @79
    cA
    @4
    @52
    co
    #
    @53
    @43
    co
    @54
    @39
    cX
    cR
    @52
    @43
    cA
    @4
    @5
    nrginvrcn.x
    @82
    @76
    @73
    @59
    @74
    @75
    ringsubdi
    @39
    @83
    @51
    @53
    @43
    @39
    @72
    @31
    @83
    @51
    wceq
    @73
    @58
    cR
    @52
    cU
    @51
    cI
    cA
    nrginvrcn.u
    nrginvrcn.i
    @82
    @51
    eqid
    #
    unitrinv
    syl2anc
    oveq1d
    eqtrd
    fveq2d
    eqtr3d
    oveq1d
    @39
    @54
    @1
    @52
    co
    #
    cN
    cfv
    #
    @56
    @45
    @39
    @27
    @54
    cX
    wcel
    #
    @62
    @86
    @56
    wceq
    @81
    @39
    @68
    @51
    cX
    wcel
    #
    @53
    cX
    wcel
    #
    @87
    @71
    @39
    @72
    @88
    @73
    cX
    cR
    @51
    nrginvrcn.x
    @84
    ringidcl
    syl
    #
    @39
    @72
    @23
    @70
    @89
    @73
    @59
    @75
    cX
    cR
    @52
    cA
    @5
    nrginvrcn.x
    @82
    ringcl
    syl3anc
    #
    cX
    cR
    @43
    @51
    @53
    nrginvrcn.x
    @76
    grpsubcl
    syl3anc
    @64
    @54
    @1
    cR
    @52
    cN
    cX
    nrginvrcn.x
    nrginvrcn.n
    @82
    nmmul
    syl3anc
    @39
    @85
    @44
    cN
    @39
    @85
    @51
    @1
    @52
    co
    #
    @53
    @1
    @52
    co
    #
    @43
    co
    @44
    @39
    cX
    cR
    @52
    @43
    @51
    @53
    @1
    nrginvrcn.x
    @82
    @76
    @73
    @90
    @91
    @64
    rngsubdir
    @39
    @92
    @1
    @93
    cA
    @43
    @39
    @72
    @62
    @92
    @1
    wceq
    @73
    @64
    cX
    cR
    @52
    @51
    @1
    nrginvrcn.x
    @82
    @84
    ringlidm
    syl2anc
    @39
    @93
    cA
    @5
    @1
    @52
    co
    #
    @52
    co
    #
    cA
    @51
    @52
    co
    #
    cA
    @39
    @72
    @23
    @70
    @62
    @93
    @95
    wceq
    @73
    @59
    @75
    @64
    cX
    cR
    @52
    cA
    @5
    @1
    nrginvrcn.x
    @82
    ringass
    syl13anc
    @39
    @94
    @51
    cA
    @52
    @39
    @72
    @37
    @94
    @51
    wceq
    @73
    @63
    cR
    @52
    cU
    @51
    cI
    @1
    nrginvrcn.u
    nrginvrcn.i
    @82
    @84
    unitlinv
    syl2anc
    oveq2d
    @39
    @72
    @23
    @96
    cA
    wceq
    @73
    @59
    cX
    cR
    @52
    @51
    cA
    nrginvrcn.x
    @82
    @84
    ringridm
    syl2anc
    3eqtrd
    oveq12d
    eqtrd
    fveq2d
    eqtr3d
    3eqtrd
    @39
    @45
    @41
    @48
    @39
    @45
    @39
    @22
    @44
    cX
    wcel
    #
    @45
    cr
    wcel
    @57
    @39
    @68
    @62
    @23
    @97
    @71
    @64
    @59
    cX
    cR
    @43
    @1
    cA
    nrginvrcn.x
    @76
    grpsubcl
    syl3anc
    @44
    cR
    cN
    cX
    nrginvrcn.x
    nrginvrcn.n
    nmcl
    syl2anc
    #
    recnd
    @39
    @41
    @39
    @41
    @39
    @14
    @40
    wph
    @26
    @38
    @33
    adantr
    #
    @39
    @22
    @62
    @1
    @24
    wne
    #
    @40
    crp
    wcel
    @57
    @64
    @39
    @30
    @37
    @100
    wph
    @30
    @38
    nrginvrcn.z
    adantr
    @63
    @1
    cR
    cU
    @24
    nrginvrcn.u
    @32
    nzrunit
    syl2anc
    @1
    cR
    cN
    cX
    @24
    nrginvrcn.x
    nrginvrcn.n
    @32
    nmrpcl
    syl3anc
    rpmulcld
    #
    rpred
    #
    recnd
    @78
    @39
    @41
    @101
    rpne0d
    divmuld
    mpbird
    @39
    @2
    @45
    @41
    cdiv
    @39
    @22
    @23
    @62
    @2
    @45
    wceq
    @57
    @59
    @64
    cA
    @1
    cD
    cR
    @43
    cN
    cX
    nrginvrcn.n
    nrginvrcn.x
    @76
    nrginvrcn.d
    ngpdsr
    syl3anc
    #
    oveq1d
    @39
    @22
    @69
    @70
    @6
    @48
    wceq
    @57
    @74
    @75
    @4
    @5
    cD
    cR
    @43
    cN
    cX
    nrginvrcn.n
    nrginvrcn.x
    @76
    nrginvrcn.d
    ngpds
    syl3anc
    3eqtr4rd
    @39
    @42
    cB
    clt
    wbr
    @2
    @41
    cB
    cmul
    co
    #
    clt
    wbr
    @39
    @2
    cT
    @104
    @39
    @2
    @45
    cr
    @103
    @98
    eqeltrd
    #
    @39
    cT
    wph
    @0
    @38
    @36
    adantr
    rpred
    #
    @39
    @41
    cB
    @102
    @39
    cB
    wph
    cB
    crp
    wcel
    @38
    nrginvrcn.b
    adantr
    rpred
    #
    remulcld
    #
    wph
    @37
    @3
    simprr
    #
    @39
    cT
    @15
    @18
    cmul
    co
    #
    @104
    @106
    @39
    @110
    @39
    @15
    @18
    wph
    @20
    @38
    @34
    adantr
    #
    @39
    @14
    @99
    rphalfcld
    #
    rpmulcld
    rpred
    @108
    @39
    cT
    @19
    @110
    cle
    nrginvrcn.t
    @39
    @17
    @15
    cle
    wbr
    #
    @19
    @110
    cle
    wbr
    @39
    c1
    cr
    wcel
    #
    @15
    cr
    wcel
    #
    @113
    1re
    @39
    @15
    @111
    rpred
    #
    c1
    @15
    min2
    sylancr
    @39
    @17
    @15
    @18
    @39
    @17
    wph
    @21
    @38
    @35
    adantr
    rpred
    #
    @116
    @112
    lemul1d
    mpbid
    syl5eqbr
    @39
    @110
    @15
    @40
    cmul
    co
    @104
    clt
    @39
    @18
    @40
    @15
    @39
    @18
    @112
    rpred
    #
    @65
    @111
    @39
    @18
    @40
    clt
    wbr
    @18
    @18
    caddc
    co
    #
    @40
    @18
    caddc
    co
    #
    clt
    wbr
    @39
    @119
    @14
    @120
    clt
    @39
    @14
    @61
    2halvesd
    @39
    @14
    @40
    cmin
    co
    #
    @18
    clt
    wbr
    @14
    @120
    clt
    wbr
    @39
    @121
    @2
    @18
    @39
    @14
    @40
    @60
    @65
    resubcld
    @105
    @118
    @39
    @121
    cA
    @1
    @43
    co
    cN
    cfv
    #
    @2
    cle
    @39
    @22
    @23
    @62
    @121
    @122
    cle
    wbr
    @57
    @59
    @64
    cA
    @1
    cR
    @43
    cN
    cX
    nrginvrcn.x
    nrginvrcn.n
    @76
    nm2dif
    syl3anc
    @39
    @22
    @23
    @62
    @2
    @122
    wceq
    @57
    @59
    @64
    cA
    @1
    cD
    cR
    @43
    cN
    cX
    nrginvrcn.n
    nrginvrcn.x
    @76
    nrginvrcn.d
    ngpds
    syl3anc
    breqtrrd
    @39
    @2
    cT
    @18
    @105
    @106
    @118
    @109
    @39
    cT
    c1
    @18
    cmul
    co
    #
    @18
    cle
    @39
    cT
    @19
    @123
    cle
    nrginvrcn.t
    @39
    @17
    c1
    cle
    wbr
    #
    @19
    @123
    cle
    wbr
    @39
    @114
    @115
    @124
    1re
    @116
    c1
    @15
    min1
    sylancr
    @39
    @17
    c1
    @18
    @117
    @39
    1red
    @112
    lemul1d
    mpbid
    syl5eqbr
    @39
    @18
    @39
    @18
    @118
    recnd
    mulid2d
    breqtrd
    ltletrd
    lelttrd
    @39
    @14
    @40
    @18
    @60
    @65
    @118
    ltsubadd2d
    mpbid
    eqbrtrd
    @39
    @18
    @40
    @18
    @118
    @65
    @118
    ltadd1d
    mpbird
    ltmul2dd
    @39
    @14
    @40
    cB
    @61
    @66
    @39
    cB
    @107
    recnd
    mul32d
    breqtrrd
    lelttrd
    lttrd
    @39
    @2
    cB
    @41
    @105
    @107
    @101
    ltdivmuld
    mpbird
    eqbrtrd
    expr
    ralrimiva
    @13
    @9
    vx
    cT
    crp
    @10
    cT
    wceq
    #
    @12
    @8
    vy
    cU
    @125
    @11
    @3
    @7
    @10
    cT
    @2
    clt
    breq2
    imbi1d
    ralbidv
    rspcev
    syl2anc
end
