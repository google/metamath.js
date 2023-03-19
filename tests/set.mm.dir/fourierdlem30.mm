include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "cmul.mm"
include "cmin.mm"
include "citg.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "recnd.mm"
include "cc0.mm"
include "c1.mm"
include "0red.mm"
include "1red.mm"
include "wbr.mm"
include "0lt1.mm"
include "a1i.mm"
include "caddc.mm"
include "cr.mm"
include "abscld.mm"
include "syl5eqel.mm"
include "readdcld.mm"
include "cc.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "negcld.mm"
include "mulcld.mm"
include "itgcl.mm"
include "rpred.mm"
include "rpne0d.mm"
include "redivcld.mm"
include "cle.mm"
include "absge0d.mm"
include "syl6breqr.mm"
include "addge0d.mm"
include "divge0d.mm"
include "addge02d.mm"
include "mpbid.mm"
include "letrd.mm"
include "ltletrd.mm"
include "gt0ne0d.mm"
include "divnegd.mm"
include "oveq2d.mm"
include "divassd.mm"
include "eqtr4d.mm"
include "oveq12d.mm"
include "divsubdird.mm"
include "reccld.mm"
include "itgmulc2.mm"
include "divrec2d.mm"
include "adantr.mm"
include "wne.mm"
include "3eqtr2d.mm"
include "itgeq2dv.mm"
include "3eqtr4rd.mm"
include "subcld.mm"
include "fveq2d.mm"
include "absdivd.mm"
include "ltled.mm"
include "absidd.mm"
include "3eqtrd.mm"
include "elrpd.mm"
include "abs2dif2d.mm"
include "absmuld.mm"
include "absnegd.mm"
include "eqbrtrd.mm"
include "lemul2ad.mm"
include "mulid1d.mm"
include "breqtrd.mm"
include "le2addd.mm"
include "leadd1dd.mm"
include "lediv1dd.mm"
include "ltp1d.mm"
include "lelttrd.mm"
include "ge0p1rpd.mm"
include "eqcomi.mm"
include "oveq12i.mm"
include "lediv2ad.mm"
include "oveq1i.mm"
include "wceq.mm"
include "oveq1.mm"
include "adantl.mm"
include "addcld.mm"
include "rpcnd.mm"
include "div0d.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "0p1e1.mm"
include "syl6eq.mm"
include "ax-1ne0.mm"
include "eqnetrd.mm"
include "rpgt0d.mm"
include "wn.mm"
include "crp.mm"
include "neqne.mm"
include "ne0gt0d.mm"
include "rpdivcld.mm"
include "1rp.mm"
include "rpaddcld.mm"
include "ltdiv23d.mm"
include "pm2.61dan.mm"
include "syl5eqbr.mm"

theorem fourierdlem30
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vk: setvar k
  assume fourierdlem30.ibl: |- ( ph -> ( x e. I |-> ( F x. -u G ) ) e. L^1 )
  assume fourierlemreimleblemlte22.f: |- ( ( ph /\ x e. I ) -> F e. CC )
  assume fourierdlem30.g: |- ( ( ph /\ x e. I ) -> G e. CC )
  assume fourierdlem30.a: |- ( ph -> A e. CC )
  assume fourierdlem30.x: |- X = ( abs ` A )
  assume fourierdlem30.c: |- ( ph -> C e. CC )
  assume fourierdlem30.y: |- Y = ( abs ` C )
  assume fourierdlem30.z: |- Z = ( abs ` S. I ( F x. -u G ) _d x )
  assume fourierdlem30.e: |- ( ph -> E e. RR+ )
  assume fourierdlem30.r: |- ( ph -> R e. RR )
  assume fourierdlem30.ler: |- ( ph -> ( ( ( ( X + Y ) + Z ) / E ) + 1 ) <_ R )
  assume fourierdlem30.b: |- ( ph -> B e. CC )
  assume fourierdlem30.12: |- ( ph -> ( abs ` B ) <_ 1 )
  assume fourierdlem30.d: |- ( ph -> D e. CC )
  assume fourierdlem30.14: |- ( ph -> ( abs ` D ) <_ 1 )

  disjoint I x
  disjoint R x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( abs ` ( ( ( A x. -u ( B / R ) ) - ( C x. -u ( D / R ) ) ) - S. I ( F x. -u ( G / R ) ) _d x ) ) < E )

  proof
    wph
    cA
    cB
    cR
    cdiv
    co
    cneg
    #
    cmul
    co
    #
    cC
    cD
    cR
    cdiv
    co
    cneg
    #
    cmul
    co
    #
    cmin
    co
    #
    vx
    cI
    cF
    cG
    cR
    cdiv
    co
    cneg
    #
    cmul
    co
    #
    citg
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cA
    cB
    cneg
    #
    cmul
    co
    #
    cC
    cD
    cneg
    #
    cmul
    co
    #
    cmin
    co
    #
    vx
    cI
    cF
    cG
    cneg
    #
    cmul
    co
    #
    citg
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cR
    cdiv
    co
    #
    cE
    clt
    wph
    @9
    @18
    cR
    cdiv
    co
    #
    cabs
    cfv
    @19
    cR
    cabs
    cfv
    #
    cdiv
    co
    @20
    wph
    @8
    @21
    cabs
    wph
    @8
    @14
    cR
    cdiv
    co
    #
    @17
    cR
    cdiv
    co
    #
    cmin
    co
    @21
    wph
    @4
    @23
    @7
    @24
    cmin
    wph
    @4
    @11
    cR
    cdiv
    co
    #
    @13
    cR
    cdiv
    co
    #
    cmin
    co
    @23
    wph
    @1
    @25
    @3
    @26
    cmin
    wph
    @1
    cA
    @10
    cR
    cdiv
    co
    #
    cmul
    co
    @25
    wph
    @0
    @27
    cA
    cmul
    wph
    cB
    cR
    fourierdlem30.b
    wph
    cR
    fourierdlem30.r
    recnd
    #
    wph
    cR
    wph
    cc0
    c1
    cR
    wph
    0red
    #
    wph
    1red
    #
    fourierdlem30.r
    cc0
    c1
    clt
    wbr
    wph
    0lt1
    a1i
    wph
    c1
    cX
    cY
    caddc
    co
    #
    cZ
    caddc
    co
    #
    cE
    cdiv
    co
    #
    c1
    caddc
    co
    #
    cR
    @30
    wph
    @33
    c1
    wph
    @32
    cE
    wph
    @31
    cZ
    wph
    cX
    cY
    wph
    cX
    cA
    cabs
    cfv
    #
    cr
    fourierdlem30.x
    wph
    cA
    fourierdlem30.a
    abscld
    #
    syl5eqel
    #
    wph
    cY
    cC
    cabs
    cfv
    #
    cr
    fourierdlem30.y
    wph
    cC
    fourierdlem30.c
    abscld
    #
    syl5eqel
    #
    readdcld
    #
    wph
    cZ
    @17
    cabs
    cfv
    #
    cr
    fourierdlem30.z
    wph
    @17
    wph
    vx
    cI
    @16
    cc
    wph
    vx
    cv
    cI
    wcel
    #
    wa
    #
    cF
    @15
    fourierlemreimleblemlte22.f
    @44
    cG
    fourierdlem30.g
    negcld
    #
    mulcld
    #
    fourierdlem30.ibl
    itgcl
    #
    abscld
    #
    syl5eqel
    #
    readdcld
    #
    wph
    cE
    fourierdlem30.e
    rpred
    #
    wph
    cE
    fourierdlem30.e
    rpne0d
    #
    redivcld
    #
    @30
    readdcld
    #
    fourierdlem30.r
    wph
    cc0
    @33
    cle
    wbr
    c1
    @34
    cle
    wbr
    wph
    @32
    cE
    @50
    fourierdlem30.e
    wph
    @31
    cZ
    @41
    @49
    wph
    cX
    cY
    @37
    @40
    wph
    cc0
    @35
    cX
    cle
    wph
    cA
    fourierdlem30.a
    absge0d
    #
    fourierdlem30.x
    syl6breqr
    wph
    cc0
    @38
    cY
    cle
    wph
    cC
    fourierdlem30.c
    absge0d
    #
    fourierdlem30.y
    syl6breqr
    addge0d
    wph
    cc0
    @42
    cZ
    cle
    wph
    @17
    @47
    absge0d
    fourierdlem30.z
    syl6breqr
    addge0d
    #
    divge0d
    #
    wph
    c1
    @33
    @30
    @53
    addge02d
    mpbid
    fourierdlem30.ler
    letrd
    ltletrd
    #
    gt0ne0d
    #
    divnegd
    oveq2d
    wph
    cA
    @10
    cR
    fourierdlem30.a
    wph
    cB
    fourierdlem30.b
    negcld
    #
    @28
    @60
    divassd
    eqtr4d
    wph
    @3
    cC
    @12
    cR
    cdiv
    co
    #
    cmul
    co
    @26
    wph
    @2
    @62
    cC
    cmul
    wph
    cD
    cR
    fourierdlem30.d
    @28
    @60
    divnegd
    oveq2d
    wph
    cC
    @12
    cR
    fourierdlem30.c
    wph
    cD
    fourierdlem30.d
    negcld
    #
    @28
    @60
    divassd
    eqtr4d
    oveq12d
    wph
    @11
    @13
    cR
    wph
    cA
    @10
    fourierdlem30.a
    @61
    mulcld
    #
    wph
    cC
    @12
    fourierdlem30.c
    @63
    mulcld
    #
    @28
    @60
    divsubdird
    eqtr4d
    wph
    c1
    cR
    cdiv
    co
    #
    @17
    cmul
    co
    vx
    cI
    @66
    @16
    cmul
    co
    #
    citg
    @24
    @7
    wph
    vx
    cI
    @16
    @66
    cc
    wph
    cR
    @28
    @60
    reccld
    @46
    fourierdlem30.ibl
    itgmulc2
    wph
    @17
    cR
    @47
    @28
    @60
    divrec2d
    wph
    vx
    cI
    @6
    @67
    @44
    @6
    cF
    @15
    cR
    cdiv
    co
    #
    cmul
    co
    @16
    cR
    cdiv
    co
    @67
    @44
    @5
    @68
    cF
    cmul
    @44
    cG
    cR
    fourierdlem30.g
    wph
    cR
    cc
    wcel
    @43
    @28
    adantr
    #
    wph
    cR
    cc0
    wne
    @43
    @60
    adantr
    #
    divnegd
    oveq2d
    @44
    cF
    @15
    cR
    fourierlemreimleblemlte22.f
    @45
    @69
    @70
    divassd
    @44
    @16
    cR
    @46
    @69
    @70
    divrec2d
    3eqtr2d
    itgeq2dv
    3eqtr4rd
    oveq12d
    wph
    @14
    @17
    cR
    wph
    @11
    @13
    @64
    @65
    subcld
    #
    @47
    @28
    @60
    divsubdird
    eqtr4d
    fveq2d
    wph
    @18
    cR
    wph
    @14
    @17
    @71
    @47
    subcld
    #
    @28
    @60
    absdivd
    wph
    @22
    cR
    @19
    cdiv
    wph
    cR
    fourierdlem30.r
    wph
    cc0
    cR
    @29
    fourierdlem30.r
    @59
    ltled
    absidd
    oveq2d
    3eqtrd
    wph
    @20
    @35
    @38
    caddc
    co
    #
    @42
    caddc
    co
    #
    cR
    cdiv
    co
    #
    cE
    wph
    @19
    cR
    wph
    @18
    @72
    abscld
    #
    fourierdlem30.r
    @60
    redivcld
    wph
    @74
    cR
    wph
    @73
    @42
    wph
    @35
    @38
    @36
    @39
    readdcld
    #
    @48
    readdcld
    #
    fourierdlem30.r
    @60
    redivcld
    #
    @51
    wph
    @19
    @74
    cR
    @76
    @78
    wph
    cR
    fourierdlem30.r
    @59
    elrpd
    #
    wph
    @19
    @14
    cabs
    cfv
    #
    @42
    caddc
    co
    @74
    @76
    wph
    @81
    @42
    wph
    @14
    @71
    abscld
    #
    @48
    readdcld
    @78
    wph
    @14
    @17
    @71
    @47
    abs2dif2d
    wph
    @81
    @73
    @42
    @82
    @77
    @48
    wph
    @81
    @11
    cabs
    cfv
    #
    @13
    cabs
    cfv
    #
    caddc
    co
    @73
    @82
    wph
    @83
    @84
    wph
    @11
    @64
    abscld
    #
    wph
    @13
    @65
    abscld
    #
    readdcld
    @77
    wph
    @11
    @13
    @64
    @65
    abs2dif2d
    wph
    @83
    @84
    @35
    @38
    @85
    @86
    @36
    @39
    wph
    @83
    @35
    @10
    cabs
    cfv
    #
    cmul
    co
    #
    @35
    cle
    wph
    cA
    @10
    fourierdlem30.a
    @61
    absmuld
    wph
    @88
    @35
    c1
    cmul
    co
    @35
    cle
    wph
    @87
    c1
    @35
    wph
    @10
    @61
    abscld
    @30
    @36
    @55
    wph
    @87
    cB
    cabs
    cfv
    c1
    cle
    wph
    cB
    fourierdlem30.b
    absnegd
    fourierdlem30.12
    eqbrtrd
    lemul2ad
    wph
    @35
    wph
    @35
    @36
    recnd
    mulid1d
    breqtrd
    eqbrtrd
    wph
    @84
    @38
    @12
    cabs
    cfv
    #
    cmul
    co
    #
    @38
    cle
    wph
    cC
    @12
    fourierdlem30.c
    @63
    absmuld
    wph
    @90
    @38
    c1
    cmul
    co
    @38
    cle
    wph
    @89
    c1
    @38
    wph
    @12
    @63
    abscld
    @30
    @39
    @56
    wph
    @89
    cD
    cabs
    cfv
    c1
    cle
    wph
    cD
    fourierdlem30.d
    absnegd
    fourierdlem30.14
    eqbrtrd
    lemul2ad
    wph
    @38
    wph
    @38
    @39
    recnd
    mulid1d
    breqtrd
    eqbrtrd
    le2addd
    letrd
    leadd1dd
    letrd
    lediv1dd
    wph
    @75
    @74
    @34
    cdiv
    co
    #
    cE
    @79
    wph
    @74
    @34
    @78
    @54
    wph
    @34
    wph
    cc0
    @33
    @34
    @29
    @53
    @54
    @58
    wph
    @33
    @53
    ltp1d
    #
    lelttrd
    gt0ne0d
    redivcld
    @51
    wph
    @34
    cR
    @74
    wph
    @33
    @53
    @58
    ge0p1rpd
    @80
    @78
    wph
    cc0
    @32
    @74
    cle
    @57
    @73
    @31
    @42
    cZ
    caddc
    @35
    cX
    @38
    cY
    caddc
    cX
    @35
    fourierdlem30.x
    eqcomi
    cY
    @38
    fourierdlem30.y
    eqcomi
    oveq12i
    cZ
    @42
    fourierdlem30.z
    eqcomi
    oveq12i
    #
    syl6breqr
    fourierdlem30.ler
    lediv2ad
    wph
    @91
    @32
    @34
    cdiv
    co
    #
    cE
    clt
    @74
    @32
    @34
    cdiv
    @93
    oveq1i
    wph
    @32
    cc0
    wceq
    #
    @94
    cE
    clt
    wbr
    wph
    @95
    wa
    #
    @94
    cc0
    cE
    clt
    @96
    @94
    cc0
    @34
    cdiv
    co
    #
    cc0
    @95
    @94
    @97
    wceq
    wph
    @32
    cc0
    @34
    cdiv
    oveq1
    adantl
    @96
    @34
    wph
    @34
    cc
    wcel
    @95
    wph
    @33
    c1
    wph
    @33
    @53
    recnd
    wph
    c1
    @30
    recnd
    addcld
    adantr
    @96
    @34
    c1
    cc0
    @96
    @34
    cc0
    c1
    caddc
    co
    c1
    @96
    @33
    cc0
    c1
    caddc
    @96
    @33
    cc0
    cE
    cdiv
    co
    #
    cc0
    @95
    @33
    @98
    wceq
    wph
    @32
    cc0
    cE
    cdiv
    oveq1
    adantl
    @96
    cE
    wph
    cE
    cc
    wcel
    @95
    wph
    cE
    fourierdlem30.e
    rpcnd
    adantr
    wph
    cE
    cc0
    wne
    @95
    @52
    adantr
    div0d
    eqtrd
    oveq1d
    0p1e1
    syl6eq
    c1
    cc0
    wne
    @96
    ax-1ne0
    a1i
    eqnetrd
    div0d
    eqtrd
    wph
    cc0
    cE
    clt
    wbr
    @95
    wph
    cE
    fourierdlem30.e
    rpgt0d
    adantr
    eqbrtrd
    wph
    @95
    wn
    #
    wa
    #
    @32
    cE
    @34
    wph
    @32
    cr
    wcel
    @99
    @50
    adantr
    #
    wph
    cE
    crp
    wcel
    @99
    fourierdlem30.e
    adantr
    #
    @100
    @33
    c1
    @100
    @32
    cE
    @100
    @32
    @101
    @100
    @32
    @101
    wph
    cc0
    @32
    cle
    wbr
    @99
    @57
    adantr
    @99
    @32
    cc0
    wne
    wph
    @32
    cc0
    neqne
    adantl
    ne0gt0d
    elrpd
    @102
    rpdivcld
    c1
    crp
    wcel
    @100
    1rp
    a1i
    rpaddcld
    wph
    @33
    @34
    clt
    wbr
    @99
    @92
    adantr
    ltdiv23d
    pm2.61dan
    syl5eqbr
    lelttrd
    lelttrd
    eqbrtrd
end
