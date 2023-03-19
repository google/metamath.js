include "cabs.mm"
include "cfv.mm"
include "cexp.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "c1.mm"
include "cmul.mm"
include "cmin.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "csu.mm"
include "cle.mm"
include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "knoppndvlem3.mm"
include "simpld.mm"
include "recnd.mm"
include "abscld.mm"
include "reexpcld.mm"
include "2re.mm"
include "a1i.mm"
include "wne.mm"
include "2ne0.mm"
include "redivcld.mm"
include "1red.mm"
include "nnred.mm"
include "remulcld.mm"
include "resubcld.mm"
include "wa.mm"
include "0red.mm"
include "0lt1.mm"
include "knoppndvlem12.mm"
include "simprd.mm"
include "lttrd.mm"
include "jca.mm"
include "gt0ne0.mm"
include "syl.mm"
include "cneg.mm"
include "wceq.mm"
include "nn0zd.mm"
include "knoppndvlem1.mm"
include "eqeltrd.mm"
include "knoppcnlem3.mm"
include "caddc.mm"
include "peano2zd.mm"
include "subcld.mm"
include "knoppndvlem5.mm"
include "remulcl.mm"
include "resubcl.mm"
include "1cnd.mm"
include "subdid.mm"
include "mulid1d.mm"
include "oveq1d.mm"
include "leidd.mm"
include "eqbrtrd.mm"
include "abssubd.mm"
include "knoppndvlem10.mm"
include "eqtrd.mm"
include "eqcomd.mm"
include "breqtrd.mm"
include "knoppndvlem14.mm"
include "le2subd.mm"
include "letrd.mm"
include "abs2difd.mm"
include "knoppndvlem6.mm"
include "cn0.mm"
include "cuz.mm"
include "elnn0uz.mm"
include "sylib.mm"
include "cn.mm"
include "adantr.mm"
include "elfznn0.mm"
include "adantl.mm"
include "fveq2.mm"
include "fsumm1.mm"
include "oveq12d.mm"
include "subadd4d.mm"
include "fveq2d.mm"

theorem knoppndvlem15
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cT: class T
  let vi: setvar i
  let vn: setvar n
  let cF: class F
  let cJ: class J
  let cM: class M
  let cN: class N
  let cW: class W
  assume knoppndvlem15.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume knoppndvlem15.f: |- F = ( y e. RR |-> ( n e. NN0 |-> ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) )
  assume knoppndvlem15.w: |- W = ( w e. RR |-> sum_ i e. NN0 ( ( F ` w ) ` i ) )
  assume knoppndvlem15.a: |- A = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. M )
  assume knoppndvlem15.b: |- B = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. ( M + 1 ) )
  assume knoppndvlem15.c: |- ( ph -> C e. ( -u 1 (,) 1 ) )
  assume knoppndvlem15.j: |- ( ph -> J e. NN0 )
  assume knoppndvlem15.m: |- ( ph -> M e. ZZ )
  assume knoppndvlem15.n: |- ( ph -> N e. NN )
  assume knoppndvlem15.1: |- ( ph -> 1 < ( N x. ( abs ` C ) ) )

  disjoint A i
  disjoint A n
  disjoint A w
  disjoint A y
  disjoint i n
  disjoint i w
  disjoint i y
  disjoint n w
  disjoint n y
  disjoint w y
  disjoint A x
  disjoint i x
  disjoint w x
  disjoint B i
  disjoint B n
  disjoint B w
  disjoint B y
  disjoint B x
  disjoint C i
  disjoint C n
  disjoint C y
  disjoint F i
  disjoint F w
  disjoint J i
  disjoint J n
  disjoint J y
  disjoint J x
  disjoint M n
  disjoint M y
  disjoint M x
  disjoint N i
  disjoint N n
  disjoint N y
  disjoint N x
  disjoint T n
  disjoint T y
  disjoint i ph
  disjoint n ph
  disjoint ph w
  disjoint ph y
  assert |- ( ph -> ( ( ( ( abs ` C ) ^ J ) / 2 ) x. ( 1 - ( 1 / ( ( ( 2 x. N ) x. ( abs ` C ) ) - 1 ) ) ) ) <_ ( abs ` ( ( W ` B ) - ( W ` A ) ) ) )

  proof
    wph
    cC
    cabs
    cfv
    #
    cJ
    cexp
    co
    #
    c2
    cdiv
    co
    #
    c1
    c1
    c2
    cN
    cmul
    co
    #
    @0
    cmul
    co
    #
    c1
    cmin
    co
    #
    cdiv
    co
    #
    cmin
    co
    #
    cmul
    co
    #
    cc0
    cJ
    c1
    cmin
    co
    #
    cfz
    co
    #
    vi
    cv
    #
    cB
    cF
    cfv
    #
    cfv
    #
    vi
    csu
    #
    @10
    @11
    cA
    cF
    cfv
    #
    cfv
    #
    vi
    csu
    #
    cmin
    co
    #
    cJ
    @15
    cfv
    #
    cJ
    @12
    cfv
    #
    cmin
    co
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cB
    cW
    cfv
    #
    cA
    cW
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cle
    wph
    @8
    @21
    @18
    cmin
    co
    #
    cabs
    cfv
    #
    @23
    cle
    wph
    @8
    @21
    cabs
    cfv
    #
    @18
    cabs
    cfv
    #
    cmin
    co
    #
    @29
    wph
    @2
    @7
    wph
    @1
    c2
    wph
    @0
    cJ
    wph
    cC
    wph
    cC
    wph
    cC
    cr
    wcel
    #
    @0
    c1
    clt
    wbr
    wph
    cC
    knoppndvlem15.c
    knoppndvlem3
    simpld
    #
    recnd
    abscld
    #
    knoppndvlem15.j
    reexpcld
    c2
    cr
    wcel
    wph
    2re
    a1i
    #
    c2
    cc0
    wne
    wph
    2ne0
    a1i
    redivcld
    #
    wph
    c1
    @6
    wph
    1red
    #
    wph
    c1
    @5
    @38
    wph
    @4
    c1
    wph
    @3
    @0
    wph
    c2
    cN
    @36
    wph
    cN
    knoppndvlem15.n
    nnred
    remulcld
    @35
    remulcld
    @38
    resubcld
    #
    wph
    @5
    cr
    wcel
    #
    cc0
    @5
    clt
    wbr
    #
    wa
    @5
    cc0
    wne
    wph
    @40
    @41
    @39
    wph
    cc0
    c1
    @5
    wph
    0red
    @38
    @39
    cc0
    c1
    clt
    wbr
    wph
    0lt1
    a1i
    wph
    @4
    c1
    wne
    c1
    @5
    clt
    wbr
    wph
    cC
    cN
    knoppndvlem15.c
    knoppndvlem15.n
    knoppndvlem15.1
    knoppndvlem12
    simprd
    lttrd
    jca
    @5
    gt0ne0
    syl
    redivcld
    #
    resubcld
    remulcld
    #
    wph
    @30
    @31
    wph
    @21
    wph
    @19
    @20
    wph
    @19
    wph
    vx
    vy
    cA
    cC
    cT
    vn
    cF
    cJ
    cN
    knoppndvlem15.t
    knoppndvlem15.f
    knoppndvlem15.n
    @34
    wph
    cA
    @3
    cJ
    cneg
    cexp
    co
    c2
    cdiv
    co
    #
    cM
    cmul
    co
    #
    cr
    cA
    @45
    wceq
    wph
    knoppndvlem15.a
    a1i
    wph
    cJ
    cM
    cN
    knoppndvlem15.n
    wph
    cJ
    knoppndvlem15.j
    nn0zd
    #
    knoppndvlem15.m
    knoppndvlem1
    eqeltrd
    #
    knoppndvlem15.j
    knoppcnlem3
    recnd
    #
    wph
    @20
    wph
    vx
    vy
    cB
    cC
    cT
    vn
    cF
    cJ
    cN
    knoppndvlem15.t
    knoppndvlem15.f
    knoppndvlem15.n
    @34
    wph
    cB
    @44
    cM
    c1
    caddc
    co
    #
    cmul
    co
    #
    cr
    cB
    @50
    wceq
    wph
    knoppndvlem15.b
    a1i
    wph
    cJ
    @49
    cN
    knoppndvlem15.n
    @46
    wph
    cM
    knoppndvlem15.m
    peano2zd
    #
    knoppndvlem1
    eqeltrd
    #
    knoppndvlem15.j
    knoppcnlem3
    recnd
    #
    subcld
    #
    abscld
    #
    wph
    @18
    wph
    @14
    @17
    wph
    @14
    wph
    vx
    vy
    cB
    cC
    cT
    vi
    vn
    cF
    @9
    cN
    knoppndvlem15.t
    knoppndvlem15.f
    @52
    @34
    knoppndvlem15.n
    knoppndvlem5
    recnd
    #
    wph
    @17
    wph
    vx
    vy
    cA
    cC
    cT
    vi
    vn
    cF
    @9
    cN
    knoppndvlem15.t
    knoppndvlem15.f
    @47
    @34
    knoppndvlem15.n
    knoppndvlem5
    recnd
    #
    subcld
    #
    abscld
    #
    resubcld
    #
    wph
    @28
    wph
    @21
    @18
    @54
    @58
    subcld
    abscld
    wph
    @8
    @2
    @2
    @6
    cmul
    co
    #
    cmin
    co
    #
    @32
    @43
    wph
    @2
    cr
    wcel
    #
    @61
    cr
    wcel
    #
    wa
    @62
    cr
    wcel
    wph
    @63
    @64
    @37
    wph
    @63
    @6
    cr
    wcel
    #
    wa
    @64
    wph
    @63
    @65
    @37
    @42
    jca
    @2
    @6
    remulcl
    syl
    jca
    @2
    @61
    resubcl
    syl
    #
    @60
    wph
    @8
    @2
    c1
    cmul
    co
    #
    @61
    cmin
    co
    #
    @62
    cle
    wph
    @2
    c1
    @6
    wph
    @2
    @37
    recnd
    #
    wph
    1cnd
    wph
    @6
    @42
    recnd
    subdid
    wph
    @68
    @62
    @62
    cle
    wph
    @67
    @2
    @61
    cmin
    wph
    @2
    @69
    mulid1d
    oveq1d
    wph
    @62
    @66
    leidd
    eqbrtrd
    eqbrtrd
    wph
    @2
    @31
    @30
    @61
    @37
    @59
    @55
    wph
    @2
    @6
    @37
    @42
    remulcld
    wph
    @2
    @2
    @30
    cle
    wph
    @2
    @37
    leidd
    wph
    @30
    @2
    wph
    @30
    @20
    @19
    cmin
    co
    cabs
    cfv
    @2
    wph
    @19
    @20
    @48
    @53
    abssubd
    wph
    vx
    vy
    cA
    cB
    cC
    cT
    vn
    cF
    cJ
    cM
    cN
    knoppndvlem15.t
    knoppndvlem15.f
    knoppndvlem15.a
    knoppndvlem15.b
    knoppndvlem15.c
    knoppndvlem15.j
    knoppndvlem15.m
    knoppndvlem15.n
    knoppndvlem10
    eqtrd
    eqcomd
    breqtrd
    wph
    vx
    vy
    cA
    cB
    cC
    cT
    vi
    vn
    cF
    cJ
    cM
    cN
    knoppndvlem15.t
    knoppndvlem15.f
    knoppndvlem15.a
    knoppndvlem15.b
    knoppndvlem15.c
    knoppndvlem15.j
    knoppndvlem15.m
    knoppndvlem15.n
    knoppndvlem15.1
    knoppndvlem14
    le2subd
    letrd
    wph
    @21
    @18
    @54
    @58
    abs2difd
    letrd
    wph
    @21
    @18
    @54
    @58
    abssubd
    breqtrd
    wph
    @27
    @23
    wph
    @26
    @22
    cabs
    wph
    @26
    @14
    @20
    caddc
    co
    #
    @17
    @19
    caddc
    co
    #
    cmin
    co
    #
    @22
    wph
    @24
    @70
    @25
    @71
    cmin
    wph
    @24
    cc0
    cJ
    cfz
    co
    #
    @13
    vi
    csu
    @70
    wph
    vx
    vy
    vw
    cB
    cC
    cT
    vi
    vn
    cF
    cJ
    @49
    cN
    cW
    knoppndvlem15.t
    knoppndvlem15.f
    knoppndvlem15.w
    knoppndvlem15.b
    knoppndvlem15.c
    knoppndvlem15.j
    @51
    knoppndvlem15.n
    knoppndvlem6
    wph
    @13
    @20
    vi
    cc0
    cJ
    wph
    cJ
    cn0
    wcel
    cJ
    cc0
    cuz
    cfv
    wcel
    knoppndvlem15.j
    cJ
    elnn0uz
    sylib
    #
    wph
    @11
    @73
    wcel
    #
    wa
    #
    @13
    @76
    vx
    vy
    cB
    cC
    cT
    vn
    cF
    @11
    cN
    knoppndvlem15.t
    knoppndvlem15.f
    wph
    cN
    cn
    wcel
    @75
    knoppndvlem15.n
    adantr
    #
    wph
    @33
    @75
    @34
    adantr
    #
    wph
    cB
    cr
    wcel
    @75
    @52
    adantr
    @75
    @11
    cn0
    wcel
    wph
    @11
    cJ
    elfznn0
    adantl
    #
    knoppcnlem3
    recnd
    @11
    cJ
    @12
    fveq2
    fsumm1
    eqtrd
    wph
    @25
    @73
    @16
    vi
    csu
    @71
    wph
    vx
    vy
    vw
    cA
    cC
    cT
    vi
    vn
    cF
    cJ
    cM
    cN
    cW
    knoppndvlem15.t
    knoppndvlem15.f
    knoppndvlem15.w
    knoppndvlem15.a
    knoppndvlem15.c
    knoppndvlem15.j
    knoppndvlem15.m
    knoppndvlem15.n
    knoppndvlem6
    wph
    @16
    @19
    vi
    cc0
    cJ
    @74
    @76
    @16
    @76
    vx
    vy
    cA
    cC
    cT
    vn
    cF
    @11
    cN
    knoppndvlem15.t
    knoppndvlem15.f
    @77
    @78
    wph
    cA
    cr
    wcel
    @75
    @47
    adantr
    @79
    knoppcnlem3
    recnd
    @11
    cJ
    @15
    fveq2
    fsumm1
    eqtrd
    oveq12d
    wph
    @22
    @72
    wph
    @14
    @17
    @19
    @20
    @56
    @57
    @48
    @53
    subadd4d
    eqcomd
    eqtrd
    fveq2d
    eqcomd
    breqtrd
end
