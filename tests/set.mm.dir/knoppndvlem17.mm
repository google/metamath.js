include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "cexp.mm"
include "c1.mm"
include "cmin.mm"
include "cdiv.mm"
include "cneg.mm"
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
include "cc0.mm"
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
include "mulcomd.mm"
include "oveq1d.mm"
include "crp.mm"
include "2rp.mm"
include "nnrpd.mm"
include "rpmulcld.mm"
include "nn0zd.mm"
include "znegcld.mm"
include "rpexpcld.mm"
include "rphalfcld.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "divassd.mm"
include "divcld.mm"
include "divcan7d.mm"
include "expnegd.mm"
include "oveq2d.mm"
include "1cnd.mm"
include "expcld.mm"
include "gtned.mm"
include "expne0d.mm"
include "divdiv2d.mm"
include "mulcld.mm"
include "div1d.mm"
include "cc.mm"
include "cz.mm"
include "w3a.mm"
include "wceq.mm"
include "knoppndvlem13.mm"
include "absne0d.mm"
include "3jca.mm"
include "mulexpz.mm"
include "eqcomd.mm"
include "3eqtrd.mm"
include "eqtrd.mm"
include "caddc.mm"
include "peano2zd.mm"
include "knoppndvlem1.mm"
include "eqeltrd.mm"
include "knoppcld.mm"
include "subcld.mm"
include "knoppndvlem15.mm"
include "lediv1dd.mm"
include "eqbrtrd.mm"
include "knoppndvlem16.mm"
include "breqtrd.mm"

theorem knoppndvlem17
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
  assume knoppndvlem17.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume knoppndvlem17.f: |- F = ( y e. RR |-> ( n e. NN0 |-> ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) )
  assume knoppndvlem17.w: |- W = ( w e. RR |-> sum_ i e. NN0 ( ( F ` w ) ` i ) )
  assume knoppndvlem17.a: |- A = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. M )
  assume knoppndvlem17.b: |- B = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. ( M + 1 ) )
  assume knoppndvlem17.c: |- ( ph -> C e. ( -u 1 (,) 1 ) )
  assume knoppndvlem17.j: |- ( ph -> J e. NN0 )
  assume knoppndvlem17.m: |- ( ph -> M e. ZZ )
  assume knoppndvlem17.n: |- ( ph -> N e. NN )
  assume knoppndvlem17.1: |- ( ph -> 1 < ( N x. ( abs ` C ) ) )

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
  assert |- ( ph -> ( ( ( ( 2 x. N ) x. ( abs ` C ) ) ^ J ) x. ( 1 - ( 1 / ( ( ( 2 x. N ) x. ( abs ` C ) ) - 1 ) ) ) ) <_ ( ( abs ` ( ( W ` B ) - ( W ` A ) ) ) / ( B - A ) ) )

  proof
    wph
    c2
    cN
    cmul
    co
    #
    cC
    cabs
    cfv
    #
    cmul
    co
    #
    cJ
    cexp
    co
    #
    c1
    c1
    @2
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
    @0
    cJ
    cneg
    #
    cexp
    co
    #
    c2
    cdiv
    co
    #
    cdiv
    co
    #
    @11
    cB
    cA
    cmin
    co
    #
    cdiv
    co
    cle
    wph
    @7
    @1
    cJ
    cexp
    co
    #
    c2
    cdiv
    co
    #
    @6
    cmul
    co
    #
    @14
    cdiv
    co
    #
    @15
    cle
    wph
    @20
    @7
    wph
    @20
    @6
    @18
    cmul
    co
    #
    @14
    cdiv
    co
    @6
    @18
    @14
    cdiv
    co
    #
    cmul
    co
    #
    @7
    wph
    @19
    @21
    @14
    cdiv
    wph
    @18
    @6
    wph
    @18
    wph
    @17
    c2
    wph
    @1
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
    @1
    c1
    clt
    wbr
    #
    wph
    cC
    knoppndvlem17.c
    knoppndvlem3
    #
    simpld
    #
    recnd
    #
    abscld
    #
    knoppndvlem17.j
    reexpcld
    #
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
    #
    redivcld
    #
    recnd
    #
    wph
    @6
    wph
    c1
    @5
    wph
    1red
    #
    wph
    c1
    @4
    @35
    wph
    @2
    c1
    wph
    @0
    @1
    wph
    c2
    cN
    @31
    wph
    cN
    knoppndvlem17.n
    nnred
    remulcld
    #
    @29
    remulcld
    @35
    resubcld
    #
    wph
    @4
    cr
    wcel
    #
    cc0
    @4
    clt
    wbr
    #
    wa
    @4
    cc0
    wne
    wph
    @38
    @39
    @37
    wph
    cc0
    c1
    @4
    wph
    0red
    #
    @35
    @37
    cc0
    c1
    clt
    wbr
    wph
    0lt1
    a1i
    #
    wph
    @2
    c1
    wne
    c1
    @4
    clt
    wbr
    wph
    cC
    cN
    knoppndvlem17.c
    knoppndvlem17.n
    knoppndvlem17.1
    knoppndvlem12
    simprd
    lttrd
    jca
    @4
    gt0ne0
    syl
    redivcld
    resubcld
    #
    recnd
    #
    mulcomd
    oveq1d
    wph
    @6
    @18
    @14
    @43
    @34
    wph
    @14
    wph
    @13
    wph
    @0
    @12
    wph
    c2
    cN
    c2
    crp
    wcel
    wph
    2rp
    a1i
    wph
    cN
    knoppndvlem17.n
    nnrpd
    rpmulcld
    #
    wph
    cJ
    wph
    cJ
    knoppndvlem17.j
    nn0zd
    #
    znegcld
    rpexpcld
    #
    rphalfcld
    #
    rpcnd
    #
    wph
    @14
    @47
    rpne0d
    #
    divassd
    wph
    @23
    @22
    @6
    cmul
    co
    @7
    wph
    @6
    @22
    @43
    wph
    @18
    @14
    @34
    @48
    @49
    divcld
    mulcomd
    wph
    @22
    @3
    @6
    cmul
    wph
    @22
    @17
    @13
    cdiv
    co
    #
    @3
    wph
    @17
    @13
    c2
    wph
    @17
    @30
    recnd
    #
    wph
    @13
    @46
    rpcnd
    wph
    c2
    @31
    recnd
    wph
    @13
    @46
    rpne0d
    @32
    divcan7d
    wph
    @50
    @17
    c1
    @0
    cJ
    cexp
    co
    #
    cdiv
    co
    #
    cdiv
    co
    @17
    @52
    cmul
    co
    #
    c1
    cdiv
    co
    #
    @3
    wph
    @13
    @53
    @17
    cdiv
    wph
    @0
    cJ
    wph
    @0
    @36
    recnd
    #
    wph
    @0
    @44
    rpne0d
    #
    @45
    expnegd
    oveq2d
    wph
    @17
    c1
    @52
    @51
    wph
    1cnd
    wph
    @0
    cJ
    @56
    knoppndvlem17.j
    expcld
    #
    wph
    cc0
    c1
    @40
    @41
    gtned
    wph
    @0
    cJ
    @56
    @57
    @45
    expne0d
    divdiv2d
    wph
    @55
    @54
    @52
    @17
    cmul
    co
    #
    @3
    wph
    @54
    wph
    @17
    @52
    @51
    @58
    mulcld
    div1d
    wph
    @17
    @52
    @51
    @58
    mulcomd
    wph
    @3
    @59
    wph
    @0
    cc
    wcel
    #
    @0
    cc0
    wne
    #
    wa
    #
    @1
    cc
    wcel
    #
    @1
    cc0
    wne
    #
    wa
    #
    cJ
    cz
    wcel
    #
    w3a
    @3
    @59
    wceq
    wph
    @62
    @65
    @66
    wph
    @60
    @61
    @56
    @57
    jca
    wph
    @63
    @64
    wph
    @1
    @29
    recnd
    wph
    cC
    @28
    wph
    cC
    cN
    knoppndvlem17.c
    knoppndvlem17.n
    knoppndvlem17.1
    knoppndvlem13
    absne0d
    jca
    @45
    3jca
    @0
    @1
    cJ
    mulexpz
    syl
    eqcomd
    3eqtrd
    3eqtrd
    eqtrd
    oveq1d
    eqtrd
    3eqtrd
    eqcomd
    wph
    @19
    @11
    @14
    wph
    @18
    @6
    @33
    @42
    remulcld
    wph
    @10
    wph
    @8
    @9
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
    cN
    cW
    knoppndvlem17.t
    knoppndvlem17.f
    knoppndvlem17.w
    wph
    cB
    @14
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
    @68
    wceq
    wph
    knoppndvlem17.b
    a1i
    wph
    cJ
    @67
    cN
    knoppndvlem17.n
    @45
    wph
    cM
    knoppndvlem17.m
    peano2zd
    knoppndvlem1
    eqeltrd
    knoppndvlem17.n
    @27
    wph
    @24
    @25
    @26
    simprd
    #
    knoppcld
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
    cN
    cW
    knoppndvlem17.t
    knoppndvlem17.f
    knoppndvlem17.w
    wph
    cA
    @14
    cM
    cmul
    co
    #
    cr
    cA
    @70
    wceq
    wph
    knoppndvlem17.a
    a1i
    wph
    cJ
    cM
    cN
    knoppndvlem17.n
    @45
    knoppndvlem17.m
    knoppndvlem1
    eqeltrd
    knoppndvlem17.n
    @27
    @69
    knoppcld
    subcld
    abscld
    @47
    wph
    vx
    vy
    vw
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
    cW
    knoppndvlem17.t
    knoppndvlem17.f
    knoppndvlem17.w
    knoppndvlem17.a
    knoppndvlem17.b
    knoppndvlem17.c
    knoppndvlem17.j
    knoppndvlem17.m
    knoppndvlem17.n
    knoppndvlem17.1
    knoppndvlem15
    lediv1dd
    eqbrtrd
    wph
    @14
    @16
    @11
    cdiv
    wph
    @16
    @14
    wph
    cA
    cB
    cJ
    cM
    cN
    knoppndvlem17.a
    knoppndvlem17.b
    knoppndvlem17.j
    knoppndvlem17.m
    knoppndvlem17.n
    knoppndvlem16
    eqcomd
    oveq2d
    breqtrd
end
