include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cneg.mm"
include "cexp.mm"
include "cdiv.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "wa.mm"
include "cmin.mm"
include "clt.mm"
include "wne.mm"
include "cfv.mm"
include "cabs.mm"
include "w3a.mm"
include "cr.mm"
include "wrex.mm"
include "cz.mm"
include "eqid.mm"
include "knoppndvlem19.mm"
include "wcel.mm"
include "2re.mm"
include "a1i.mm"
include "nnred.mm"
include "remulcld.mm"
include "cc0.mm"
include "2pos.mm"
include "nngt0d.mm"
include "mulgt0d.mm"
include "gt0ne0d.mm"
include "nn0zd.mm"
include "znegcld.mm"
include "reexpclzd.mm"
include "rehalfcld.mm"
include "adantr.mm"
include "simpr.mm"
include "zred.mm"
include "adantrr.mm"
include "peano2re.mm"
include "syl.mm"
include "jca.mm"
include "remulcl.mm"
include "simprr.mm"
include "cn0.mm"
include "cn.mm"
include "knoppndvlem16.mm"
include "eqbrtrd.mm"
include "3jca.mm"
include "expgt0.mm"
include "divgt0d.mm"
include "eqcomd.mm"
include "breqtrd.mm"
include "posdifd.mm"
include "mpbird.mm"
include "ltned.mm"
include "rpred.mm"
include "knoppndvlem3.mm"
include "simpld.mm"
include "recnd.mm"
include "abscld.mm"
include "reexpcld.mm"
include "wceq.mm"
include "knoppndvlem20.mm"
include "eqeltrd.mm"
include "simprd.mm"
include "knoppcld.mm"
include "subcld.mm"
include "redivcld.mm"
include "oveq2i.mm"
include "cioo.mm"
include "knoppndvlem17.mm"
include "letrd.mm"
include "breq1.mm"
include "anbi1d.mm"
include "oveq2.mm"
include "breq1d.mm"
include "neeq1.mm"
include "anbi12d.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "breq2d.mm"
include "3anbi123d.mm"
include "breq2.mm"
include "anbi2d.mm"
include "oveq1.mm"
include "neeq2.mm"
include "oveq1d.mm"
include "rspc2ev.mm"
include "rexlimddv.mm"

theorem knoppndvlem21
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cC: class C
  let cD: class D
  let cT: class T
  let vi: setvar i
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cN: class N
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  assume knoppndvlem21.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume knoppndvlem21.f: |- F = ( y e. RR |-> ( n e. NN0 |-> ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) )
  assume knoppndvlem21.w: |- W = ( w e. RR |-> sum_ i e. NN0 ( ( F ` w ) ` i ) )
  assume knoppndvlem21.g: |- G = ( 1 - ( 1 / ( ( ( 2 x. N ) x. ( abs ` C ) ) - 1 ) ) )
  assume knoppndvlem21.c: |- ( ph -> C e. ( -u 1 (,) 1 ) )
  assume knoppndvlem21.d: |- ( ph -> D e. RR+ )
  assume knoppndvlem21.e: |- ( ph -> E e. RR+ )
  assume knoppndvlem21.h: |- ( ph -> H e. RR )
  assume knoppndvlem21.j: |- ( ph -> J e. NN0 )
  assume knoppndvlem21.n: |- ( ph -> N e. NN )
  assume knoppndvlem21.1: |- ( ph -> 1 < ( N x. ( abs ` C ) ) )
  assume knoppndvlem21.2: |- ( ph -> ( ( ( 2 x. N ) ^ -u J ) / 2 ) < D )
  assume knoppndvlem21.3: |- ( ph -> E <_ ( ( ( ( 2 x. N ) x. ( abs ` C ) ) ^ J ) x. G ) )

  disjoint C i
  disjoint C n
  disjoint C y
  disjoint i n
  disjoint i y
  disjoint n y
  disjoint D a
  disjoint D b
  disjoint a b
  disjoint E a
  disjoint E b
  disjoint F i
  disjoint F w
  disjoint i w
  disjoint H a
  disjoint H b
  disjoint J a
  disjoint J b
  disjoint J i
  disjoint J n
  disjoint J w
  disjoint J y
  disjoint n w
  disjoint w y
  disjoint J x
  disjoint i x
  disjoint w x
  disjoint N a
  disjoint N b
  disjoint N i
  disjoint N n
  disjoint N w
  disjoint N y
  disjoint N x
  disjoint T n
  disjoint T y
  disjoint W a
  disjoint W b
  disjoint i ph
  disjoint n ph
  disjoint ph w
  disjoint ph y
  disjoint D m
  disjoint a m
  disjoint b m
  disjoint E m
  disjoint H m
  disjoint J m
  disjoint i m
  disjoint m n
  disjoint m w
  disjoint m y
  disjoint m x
  disjoint N m
  disjoint W m
  disjoint m ph
  assert |- ( ph -> E. a e. RR E. b e. RR ( ( a <_ H /\ H <_ b ) /\ ( ( b - a ) < D /\ a =/= b ) /\ E <_ ( ( abs ` ( ( W ` b ) - ( W ` a ) ) ) / ( b - a ) ) ) )

  proof
    wph
    c2
    cN
    cmul
    co
    #
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
    vm
    cv
    #
    cmul
    co
    #
    cH
    cle
    wbr
    #
    cH
    @3
    @4
    c1
    caddc
    co
    #
    cmul
    co
    #
    cle
    wbr
    #
    wa
    #
    va
    cv
    #
    cH
    cle
    wbr
    #
    cH
    vb
    cv
    #
    cle
    wbr
    #
    wa
    #
    @13
    @11
    cmin
    co
    #
    cD
    clt
    wbr
    #
    @11
    @13
    wne
    #
    wa
    #
    cE
    @13
    cW
    cfv
    #
    @11
    cW
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @16
    cdiv
    co
    #
    cle
    wbr
    #
    w3a
    #
    vb
    cr
    wrex
    va
    cr
    wrex
    #
    vm
    cz
    wph
    @5
    @8
    vm
    cH
    cJ
    cN
    @5
    eqid
    #
    @8
    eqid
    #
    knoppndvlem21.j
    knoppndvlem21.h
    knoppndvlem21.n
    knoppndvlem19
    wph
    @4
    cz
    wcel
    #
    @10
    wa
    wa
    #
    @5
    cr
    wcel
    #
    @8
    cr
    wcel
    #
    @10
    @8
    @5
    cmin
    co
    #
    cD
    clt
    wbr
    #
    @5
    @8
    wne
    #
    wa
    #
    cE
    @8
    cW
    cfv
    #
    @5
    cW
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @34
    cdiv
    co
    #
    cle
    wbr
    #
    w3a
    #
    w3a
    @27
    @31
    @32
    @33
    @44
    wph
    @30
    @32
    @10
    wph
    @30
    wa
    #
    @3
    @4
    wph
    @3
    cr
    wcel
    #
    @30
    wph
    @2
    wph
    @0
    @1
    wph
    c2
    cN
    c2
    cr
    wcel
    wph
    2re
    a1i
    #
    wph
    cN
    knoppndvlem21.n
    nnred
    #
    remulcld
    #
    wph
    @0
    wph
    c2
    cN
    @47
    @48
    cc0
    c2
    clt
    wbr
    wph
    2pos
    a1i
    #
    wph
    cN
    knoppndvlem21.n
    nngt0d
    mulgt0d
    #
    gt0ne0d
    wph
    cJ
    wph
    cJ
    knoppndvlem21.j
    nn0zd
    znegcld
    #
    reexpclzd
    #
    rehalfcld
    adantr
    #
    @45
    @4
    wph
    @30
    simpr
    #
    zred
    #
    remulcld
    #
    adantrr
    wph
    @30
    @33
    @10
    @45
    @46
    @7
    cr
    wcel
    #
    wa
    @33
    @45
    @46
    @58
    @54
    @45
    @4
    cr
    wcel
    @58
    @56
    @4
    peano2re
    syl
    jca
    @3
    @7
    remulcl
    syl
    #
    adantrr
    @31
    @10
    @37
    @43
    wph
    @30
    @10
    simprr
    wph
    @30
    @37
    @10
    @45
    @35
    @36
    @45
    @34
    @3
    cD
    clt
    @45
    @5
    @8
    cJ
    @4
    cN
    @28
    @29
    wph
    cJ
    cn0
    wcel
    @30
    knoppndvlem21.j
    adantr
    #
    @55
    wph
    cN
    cn
    wcel
    @30
    knoppndvlem21.n
    adantr
    #
    knoppndvlem16
    #
    wph
    @3
    cD
    clt
    wbr
    @30
    knoppndvlem21.2
    adantr
    eqbrtrd
    @45
    @5
    @8
    @57
    @45
    @5
    @8
    clt
    wbr
    cc0
    @34
    clt
    wbr
    @45
    cc0
    @3
    @34
    clt
    wph
    cc0
    @3
    clt
    wbr
    @30
    wph
    @2
    c2
    @53
    @47
    wph
    @0
    cr
    wcel
    #
    @1
    cz
    wcel
    #
    cc0
    @0
    clt
    wbr
    #
    w3a
    cc0
    @2
    clt
    wbr
    wph
    @63
    @64
    @65
    @49
    @52
    @51
    3jca
    @0
    @1
    expgt0
    syl
    @50
    divgt0d
    adantr
    @45
    @34
    @3
    @62
    eqcomd
    breqtrd
    #
    @45
    @5
    @8
    @57
    @59
    posdifd
    mpbird
    ltned
    jca
    adantrr
    wph
    @30
    @43
    @10
    @45
    cE
    @0
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
    cG
    cmul
    co
    #
    @42
    wph
    cE
    cr
    wcel
    @30
    wph
    cE
    knoppndvlem21.e
    rpred
    adantr
    wph
    @70
    cr
    wcel
    @30
    wph
    @69
    cG
    wph
    @68
    cJ
    wph
    @0
    @67
    @49
    wph
    cC
    wph
    cC
    wph
    cC
    cr
    wcel
    #
    @67
    c1
    clt
    wbr
    #
    wph
    cC
    knoppndvlem21.c
    knoppndvlem3
    #
    simpld
    #
    recnd
    abscld
    remulcld
    knoppndvlem21.j
    reexpcld
    wph
    cG
    c1
    c1
    @68
    c1
    cmin
    co
    cdiv
    co
    cmin
    co
    #
    cr
    cG
    @75
    wceq
    wph
    knoppndvlem21.g
    a1i
    wph
    @75
    wph
    cC
    cN
    knoppndvlem21.c
    knoppndvlem21.n
    knoppndvlem21.1
    knoppndvlem20
    rpred
    eqeltrd
    remulcld
    adantr
    @45
    @41
    @34
    @45
    @40
    @45
    @38
    @39
    @45
    vx
    vy
    vw
    @8
    cC
    cT
    vi
    vn
    cF
    cN
    cW
    knoppndvlem21.t
    knoppndvlem21.f
    knoppndvlem21.w
    @59
    @61
    wph
    @71
    @30
    @74
    adantr
    #
    wph
    @72
    @30
    wph
    @71
    @72
    @73
    simprd
    adantr
    #
    knoppcld
    @45
    vx
    vy
    vw
    @5
    cC
    cT
    vi
    vn
    cF
    cN
    cW
    knoppndvlem21.t
    knoppndvlem21.f
    knoppndvlem21.w
    @57
    @61
    @76
    @77
    knoppcld
    subcld
    abscld
    @45
    @34
    @3
    cr
    @62
    @54
    eqeltrd
    @45
    @34
    @66
    gt0ne0d
    redivcld
    wph
    cE
    @70
    cle
    wbr
    @30
    knoppndvlem21.3
    adantr
    @45
    @70
    @69
    @75
    cmul
    co
    #
    @42
    cle
    @70
    @78
    wceq
    @45
    cG
    @75
    @69
    cmul
    knoppndvlem21.g
    oveq2i
    a1i
    @45
    vx
    vy
    vw
    @5
    @8
    cC
    cT
    vi
    vn
    cF
    cJ
    @4
    cN
    cW
    knoppndvlem21.t
    knoppndvlem21.f
    knoppndvlem21.w
    @28
    @29
    wph
    cC
    c1
    cneg
    c1
    cioo
    co
    wcel
    @30
    knoppndvlem21.c
    adantr
    @60
    @55
    @61
    wph
    c1
    cN
    @67
    cmul
    co
    clt
    wbr
    @30
    knoppndvlem21.1
    adantr
    knoppndvlem17
    eqbrtrd
    letrd
    adantrr
    3jca
    3jca
    @26
    @44
    @6
    @14
    wa
    #
    @13
    @5
    cmin
    co
    #
    cD
    clt
    wbr
    #
    @5
    @13
    wne
    #
    wa
    #
    cE
    @20
    @39
    cmin
    co
    #
    cabs
    cfv
    #
    @80
    cdiv
    co
    #
    cle
    wbr
    #
    w3a
    va
    vb
    @5
    @8
    cr
    cr
    @11
    @5
    wceq
    #
    @15
    @79
    @19
    @83
    @25
    @87
    @88
    @12
    @6
    @14
    @11
    @5
    cH
    cle
    breq1
    anbi1d
    @88
    @17
    @81
    @18
    @82
    @88
    @16
    @80
    cD
    clt
    @11
    @5
    @13
    cmin
    oveq2
    #
    breq1d
    @11
    @5
    @13
    neeq1
    anbi12d
    @88
    @24
    @86
    cE
    cle
    @88
    @23
    @85
    @16
    @80
    cdiv
    @88
    @22
    @84
    cabs
    @88
    @21
    @39
    @20
    cmin
    @11
    @5
    cW
    fveq2
    oveq2d
    fveq2d
    @89
    oveq12d
    breq2d
    3anbi123d
    @13
    @8
    wceq
    #
    @79
    @10
    @83
    @37
    @87
    @43
    @90
    @14
    @9
    @6
    @13
    @8
    cH
    cle
    breq2
    anbi2d
    @90
    @81
    @35
    @82
    @36
    @90
    @80
    @34
    cD
    clt
    @13
    @8
    @5
    cmin
    oveq1
    #
    breq1d
    @13
    @8
    @5
    neeq2
    anbi12d
    @90
    @86
    @42
    cE
    cle
    @90
    @85
    @41
    @80
    @34
    cdiv
    @90
    @84
    @40
    cabs
    @90
    @20
    @38
    @39
    cmin
    @13
    @8
    cW
    fveq2
    oveq1d
    fveq2d
    @91
    oveq12d
    breq2d
    3anbi123d
    rspc2ev
    syl
    rexlimddv
end
