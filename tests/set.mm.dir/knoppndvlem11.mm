include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "cabs.mm"
include "c2.mm"
include "cmul.mm"
include "cexp.mm"
include "cle.mm"
include "fzfid.mm"
include "wcel.mm"
include "wa.mm"
include "cn.mm"
include "adantr.mm"
include "cr.mm"
include "clt.mm"
include "wbr.mm"
include "knoppndvlem3.mm"
include "simpld.mm"
include "cn0.mm"
include "elfznn0.mm"
include "adantl.mm"
include "knoppcnlem3.mm"
include "recnd.mm"
include "fsumsub.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "subcld.mm"
include "fsumcl.mm"
include "abscld.mm"
include "fsumrecl.mm"
include "resubcld.mm"
include "2re.mm"
include "a1i.mm"
include "nnre.mm"
include "syl.mm"
include "remulcld.mm"
include "reexpcld.mm"
include "fsumabs.mm"
include "knoppcnlem1.mm"
include "oveq12d.mm"
include "dnicld2.mm"
include "subdid.mm"
include "eqtrd.mm"
include "absmuld.mm"
include "cc.mm"
include "absexpd.mm"
include "oveq1d.mm"
include "absge0d.mm"
include "expge0d.mm"
include "dnibnd.mm"
include "lemul2ad.mm"
include "wceq.mm"
include "0le2.mm"
include "absidi.mm"
include "ax-mp.mm"
include "0red.mm"
include "1red.mm"
include "0le1.mm"
include "nnge1.mm"
include "letrd.mm"
include "absidd.mm"
include "oveq2d.mm"
include "mulassd.mm"
include "mulcld.mm"
include "mulcomd.mm"
include "mulexpd.mm"
include "3eqtrd.mm"
include "breqtrd.mm"
include "eqbrtrd.mm"
include "fsumle.mm"
include "eqeltrrd.mm"
include "fsummulc2.mm"

theorem knoppndvlem11
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cT: class T
  let vi: setvar i
  let vn: setvar n
  let cF: class F
  let cJ: class J
  let cN: class N
  assume knoppndvlem11.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume knoppndvlem11.f: |- F = ( y e. RR |-> ( n e. NN0 |-> ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) )
  assume knoppndvlem11.a: |- ( ph -> A e. RR )
  assume knoppndvlem11.b: |- ( ph -> B e. RR )
  assume knoppndvlem11.c: |- ( ph -> C e. ( -u 1 (,) 1 ) )
  assume knoppndvlem11.j: |- ( ph -> J e. NN0 )
  assume knoppndvlem11.n: |- ( ph -> N e. NN )

  disjoint A i
  disjoint A n
  disjoint A y
  disjoint i n
  disjoint i y
  disjoint n y
  disjoint A x
  disjoint i x
  disjoint B i
  disjoint B n
  disjoint B y
  disjoint B x
  disjoint C n
  disjoint C y
  disjoint J i
  disjoint J n
  disjoint J y
  disjoint N n
  disjoint N y
  disjoint N x
  disjoint T n
  disjoint T y
  disjoint i ph
  disjoint n ph
  disjoint ph y
  assert |- ( ph -> ( abs ` ( sum_ i e. ( 0 ... ( J - 1 ) ) ( ( F ` B ) ` i ) - sum_ i e. ( 0 ... ( J - 1 ) ) ( ( F ` A ) ` i ) ) ) <_ ( ( abs ` ( B - A ) ) x. sum_ i e. ( 0 ... ( J - 1 ) ) ( ( ( 2 x. N ) x. ( abs ` C ) ) ^ i ) ) )

  proof
    wph
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
    cfv
    #
    vi
    csu
    @1
    @2
    cA
    cF
    cfv
    cfv
    #
    vi
    csu
    cmin
    co
    #
    cabs
    cfv
    @1
    @3
    @4
    cmin
    co
    #
    vi
    csu
    #
    cabs
    cfv
    #
    cB
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    @1
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
    @2
    cexp
    co
    #
    vi
    csu
    #
    cmul
    co
    #
    cle
    wph
    @5
    @7
    cabs
    wph
    @7
    @5
    wph
    @1
    @3
    @4
    vi
    wph
    cc0
    @0
    fzfid
    #
    wph
    @2
    @1
    wcel
    #
    wa
    #
    @3
    @19
    vx
    vy
    cB
    cC
    cT
    vn
    cF
    @2
    cN
    knoppndvlem11.t
    knoppndvlem11.f
    wph
    cN
    cn
    wcel
    #
    @18
    knoppndvlem11.n
    adantr
    #
    wph
    cC
    cr
    wcel
    #
    @18
    wph
    @22
    @12
    c1
    clt
    wbr
    wph
    cC
    knoppndvlem11.c
    knoppndvlem3
    simpld
    #
    adantr
    #
    wph
    cB
    cr
    wcel
    @18
    knoppndvlem11.b
    adantr
    #
    @18
    @2
    cn0
    wcel
    wph
    @2
    @0
    elfznn0
    adantl
    #
    knoppcnlem3
    recnd
    #
    @19
    @4
    @19
    vx
    vy
    cA
    cC
    cT
    vn
    cF
    @2
    cN
    knoppndvlem11.t
    knoppndvlem11.f
    @21
    @24
    wph
    cA
    cr
    wcel
    @18
    knoppndvlem11.a
    adantr
    #
    @26
    knoppcnlem3
    recnd
    #
    fsumsub
    eqcomd
    fveq2d
    wph
    @8
    @1
    @6
    cabs
    cfv
    #
    vi
    csu
    #
    @16
    wph
    @7
    wph
    @1
    @6
    vi
    @17
    @19
    @3
    @4
    @27
    @29
    subcld
    #
    fsumcl
    abscld
    wph
    @1
    @30
    vi
    @17
    @19
    @6
    @32
    abscld
    #
    fsumrecl
    wph
    @10
    @15
    wph
    @9
    wph
    @9
    wph
    cB
    cA
    knoppndvlem11.b
    knoppndvlem11.a
    resubcld
    recnd
    #
    abscld
    #
    wph
    @1
    @14
    vi
    @17
    @19
    @13
    @2
    wph
    @13
    cr
    wcel
    @18
    wph
    @11
    @12
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
    @20
    cN
    cr
    wcel
    knoppndvlem11.n
    cN
    nnre
    syl
    #
    remulcld
    #
    wph
    cC
    wph
    cC
    @23
    recnd
    #
    abscld
    #
    remulcld
    adantr
    @26
    reexpcld
    #
    fsumrecl
    remulcld
    wph
    @1
    @6
    vi
    @17
    @32
    fsumabs
    wph
    @31
    @1
    @10
    @14
    cmul
    co
    #
    vi
    csu
    #
    @16
    cle
    wph
    @1
    @30
    @42
    vi
    @17
    @33
    @19
    @10
    @14
    wph
    @10
    cr
    wcel
    @18
    @35
    adantr
    #
    @41
    remulcld
    @19
    @30
    @12
    @2
    cexp
    co
    #
    @11
    @2
    cexp
    co
    #
    cB
    cmul
    co
    #
    cT
    cfv
    #
    @46
    cA
    cmul
    co
    #
    cT
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cmul
    co
    #
    @42
    cle
    @19
    @30
    cC
    @2
    cexp
    co
    #
    @51
    cmul
    co
    #
    cabs
    cfv
    #
    @53
    @19
    @6
    @55
    cabs
    @19
    @6
    @54
    @48
    cmul
    co
    #
    @54
    @50
    cmul
    co
    #
    cmin
    co
    #
    @55
    @19
    @3
    @57
    @4
    @58
    cmin
    @19
    vy
    cB
    cC
    cT
    vn
    cF
    @2
    cN
    knoppndvlem11.f
    @25
    @26
    knoppcnlem1
    @19
    vy
    cA
    cC
    cT
    vn
    cF
    @2
    cN
    knoppndvlem11.f
    @28
    @26
    knoppcnlem1
    oveq12d
    @19
    @55
    @59
    @19
    @54
    @48
    @50
    @19
    @54
    @19
    cC
    @2
    @24
    @26
    reexpcld
    recnd
    #
    @19
    @48
    @19
    vx
    @47
    cT
    knoppndvlem11.t
    @19
    @46
    cB
    @19
    @11
    @2
    wph
    @11
    cr
    wcel
    @18
    @38
    adantr
    #
    @26
    reexpcld
    #
    @25
    remulcld
    #
    dnicld2
    recnd
    #
    @19
    @50
    @19
    vx
    @49
    cT
    knoppndvlem11.t
    @19
    @46
    cA
    @62
    @28
    remulcld
    #
    dnicld2
    recnd
    #
    subdid
    eqcomd
    eqtrd
    fveq2d
    @19
    @56
    @54
    cabs
    cfv
    #
    @52
    cmul
    co
    @53
    @19
    @54
    @51
    @60
    @19
    @48
    @50
    @64
    @66
    subcld
    #
    absmuld
    @19
    @67
    @45
    @52
    cmul
    @19
    cC
    @2
    wph
    cC
    cc
    wcel
    @18
    @39
    adantr
    #
    @26
    absexpd
    oveq1d
    eqtrd
    eqtrd
    @19
    @53
    @45
    @47
    @49
    cmin
    co
    #
    cabs
    cfv
    #
    cmul
    co
    #
    @42
    cle
    @19
    @52
    @71
    @45
    @19
    @51
    @68
    abscld
    @19
    @70
    @19
    @70
    @19
    @47
    @49
    @63
    @65
    resubcld
    recnd
    abscld
    @19
    @12
    @2
    wph
    @12
    cr
    wcel
    @18
    @40
    adantr
    #
    @26
    reexpcld
    #
    @19
    @12
    @2
    @73
    @26
    @19
    cC
    @69
    absge0d
    expge0d
    @19
    vx
    @49
    @47
    cT
    knoppndvlem11.t
    @65
    @63
    dnibnd
    lemul2ad
    @19
    @72
    @45
    @46
    @10
    cmul
    co
    #
    cmul
    co
    #
    @42
    @19
    @71
    @75
    @45
    cmul
    @19
    @71
    @46
    @9
    cmul
    co
    #
    cabs
    cfv
    #
    @75
    @19
    @70
    @77
    cabs
    @19
    @77
    @70
    @19
    @46
    cB
    cA
    @19
    @46
    @62
    recnd
    #
    @19
    cB
    @25
    recnd
    @19
    cA
    @28
    recnd
    subdid
    eqcomd
    fveq2d
    @19
    @78
    @46
    cabs
    cfv
    #
    @10
    cmul
    co
    @75
    @19
    @46
    @9
    @79
    wph
    @9
    cc
    wcel
    @18
    @34
    adantr
    absmuld
    @19
    @80
    @46
    @10
    cmul
    @19
    @80
    @11
    cabs
    cfv
    #
    @2
    cexp
    co
    #
    @46
    @19
    @11
    @2
    @19
    @11
    @61
    recnd
    #
    @26
    absexpd
    wph
    @82
    @46
    wceq
    @18
    wph
    @81
    @11
    @2
    cexp
    wph
    @81
    c2
    cabs
    cfv
    #
    cN
    cabs
    cfv
    #
    cmul
    co
    @11
    wph
    c2
    cN
    wph
    c2
    @36
    recnd
    wph
    cN
    @37
    recnd
    absmuld
    wph
    @84
    c2
    @85
    cN
    cmul
    @84
    c2
    wceq
    #
    wph
    cc0
    c2
    cle
    wbr
    @86
    0le2
    c2
    2re
    absidi
    ax-mp
    a1i
    wph
    cN
    @37
    wph
    cc0
    c1
    cN
    wph
    0red
    wph
    1red
    @37
    cc0
    c1
    cle
    wbr
    wph
    0le1
    a1i
    wph
    @20
    c1
    cN
    cle
    wbr
    knoppndvlem11.n
    cN
    nnge1
    syl
    letrd
    absidd
    oveq12d
    eqtrd
    oveq1d
    adantr
    eqtrd
    oveq1d
    eqtrd
    eqtrd
    oveq2d
    @19
    @76
    @45
    @46
    cmul
    co
    #
    @10
    cmul
    co
    #
    @10
    @87
    cmul
    co
    @42
    @19
    @88
    @76
    @19
    @45
    @46
    @10
    @19
    @45
    @74
    recnd
    #
    @79
    @19
    @10
    @44
    recnd
    #
    mulassd
    eqcomd
    @19
    @87
    @10
    @19
    @45
    @46
    @89
    @79
    mulcld
    #
    @90
    mulcomd
    @19
    @87
    @14
    @10
    cmul
    @19
    @87
    @46
    @45
    cmul
    co
    #
    @14
    @19
    @45
    @46
    @89
    @79
    mulcomd
    @19
    @14
    @92
    @19
    @11
    @12
    @2
    @83
    @19
    @12
    @73
    recnd
    @26
    mulexpd
    eqcomd
    eqtrd
    #
    oveq2d
    3eqtrd
    eqtrd
    breqtrd
    eqbrtrd
    fsumle
    wph
    @16
    @43
    wph
    @1
    @14
    @10
    vi
    @17
    wph
    @10
    @35
    recnd
    @19
    @87
    @14
    cc
    @93
    @91
    eqeltrrd
    fsummulc2
    eqcomd
    breqtrd
    letrd
    eqbrtrd
end
