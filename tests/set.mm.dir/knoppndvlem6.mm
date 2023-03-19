include "cfv.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "csu.mm"
include "c1.mm"
include "caddc.mm"
include "cuz.mm"
include "cn0.mm"
include "cmin.mm"
include "cr.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "a1i.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "sumeq2sdv.mm"
include "adantl.mm"
include "c2.mm"
include "cmul.mm"
include "cneg.mm"
include "cexp.mm"
include "cdiv.mm"
include "nn0zd.mm"
include "knoppndvlem1.mm"
include "eqeltrd.mm"
include "wcel.mm"
include "sumex.mm"
include "fvmptd.mm"
include "nn0uz.mm"
include "eqid.mm"
include "peano2nn0.mm"
include "syl.mm"
include "wa.mm"
include "eqidd.mm"
include "cn.mm"
include "adantr.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "knoppndvlem3.mm"
include "simpld.mm"
include "simpr.mm"
include "knoppcnlem3.mm"
include "recnd.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "knoppndvlem4.mm"
include "seqex.mm"
include "fvex.mm"
include "breldm.mm"
include "isumsplit.mm"
include "nn0cnd.mm"
include "1cnd.mm"
include "pncand.mm"
include "oveq2d.mm"
include "sumeq1d.mm"
include "oveq1d.mm"
include "3eqtrd.mm"
include "eluznn0.mm"
include "sylan.mm"
include "knoppcnlem1.mm"
include "cz.mm"
include "cle.mm"
include "eluzle.mm"
include "wb.mm"
include "jca.mm"
include "zltp1le.mm"
include "mpbird.mm"
include "knoppndvlem2.mm"
include "dnizeq0.mm"
include "cc.mm"
include "expcld.mm"
include "mul01d.mm"
include "sumeq2dv.mm"
include "wss.mm"
include "cfn.mm"
include "wo.mm"
include "ssid.mm"
include "orcd.mm"
include "sumz.mm"
include "eqtrd.mm"
include "knoppndvlem5.mm"
include "addid1d.mm"

theorem knoppndvlem6
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cA: class A
  let cC: class C
  let cT: class T
  let vi: setvar i
  let vn: setvar n
  let cF: class F
  let cJ: class J
  let cM: class M
  let cN: class N
  let cW: class W
  assume knoppndvlem6.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume knoppndvlem6.f: |- F = ( y e. RR |-> ( n e. NN0 |-> ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) )
  assume knoppndvlem6.w: |- W = ( w e. RR |-> sum_ i e. NN0 ( ( F ` w ) ` i ) )
  assume knoppndvlem6.a: |- A = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. M )
  assume knoppndvlem6.c: |- ( ph -> C e. ( -u 1 (,) 1 ) )
  assume knoppndvlem6.j: |- ( ph -> J e. NN0 )
  assume knoppndvlem6.m: |- ( ph -> M e. ZZ )
  assume knoppndvlem6.n: |- ( ph -> N e. NN )

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
  disjoint C n
  disjoint C y
  disjoint F i
  disjoint F w
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
  disjoint ph w
  disjoint ph y
  assert |- ( ph -> ( W ` A ) = sum_ i e. ( 0 ... J ) ( ( F ` A ) ` i ) )

  proof
    wph
    cA
    cW
    cfv
    #
    cc0
    cJ
    cfz
    co
    #
    vi
    cv
    #
    cA
    cF
    cfv
    #
    cfv
    #
    vi
    csu
    #
    cJ
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    @4
    vi
    csu
    #
    caddc
    co
    #
    @5
    wph
    @0
    cn0
    @4
    vi
    csu
    #
    cc0
    @6
    c1
    cmin
    co
    #
    cfz
    co
    #
    @4
    vi
    csu
    #
    @8
    caddc
    co
    @9
    wph
    vw
    cA
    cn0
    @2
    vw
    cv
    #
    cF
    cfv
    #
    cfv
    #
    vi
    csu
    #
    @10
    cr
    cW
    cvv
    cW
    vw
    cr
    @17
    cmpt
    wceq
    wph
    knoppndvlem6.w
    a1i
    @14
    cA
    wceq
    #
    @17
    @10
    wceq
    wph
    @18
    cn0
    @16
    @4
    vi
    @18
    @2
    @15
    @3
    @14
    cA
    cF
    fveq2
    fveq1d
    sumeq2sdv
    adantl
    wph
    cA
    c2
    cN
    cmul
    co
    #
    cJ
    cneg
    cexp
    co
    c2
    cdiv
    co
    cM
    cmul
    co
    #
    cr
    cA
    @20
    wceq
    #
    wph
    knoppndvlem6.a
    a1i
    wph
    cJ
    cM
    cN
    knoppndvlem6.n
    wph
    cJ
    knoppndvlem6.j
    nn0zd
    #
    knoppndvlem6.m
    knoppndvlem1
    eqeltrd
    #
    @10
    cvv
    wcel
    wph
    cn0
    @4
    vi
    sumex
    a1i
    fvmptd
    wph
    @4
    vi
    @3
    cc0
    @6
    @7
    cn0
    nn0uz
    @7
    eqid
    wph
    cJ
    cn0
    wcel
    @6
    cn0
    wcel
    #
    knoppndvlem6.j
    cJ
    peano2nn0
    syl
    #
    wph
    @2
    cn0
    wcel
    #
    wa
    #
    @4
    eqidd
    @27
    @4
    @27
    vx
    vy
    cA
    cC
    cT
    vn
    cF
    @2
    cN
    knoppndvlem6.t
    knoppndvlem6.f
    wph
    cN
    cn
    wcel
    #
    @26
    knoppndvlem6.n
    adantr
    wph
    cC
    cr
    wcel
    #
    @26
    wph
    @29
    cC
    cabs
    cfv
    c1
    clt
    wbr
    wph
    cC
    knoppndvlem6.c
    knoppndvlem3
    simpld
    #
    adantr
    wph
    cA
    cr
    wcel
    #
    @26
    @23
    adantr
    wph
    @26
    simpr
    knoppcnlem3
    recnd
    wph
    caddc
    @3
    cc0
    cseq
    #
    @0
    cli
    wbr
    @32
    cli
    cdm
    wcel
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
    knoppndvlem6.t
    knoppndvlem6.f
    knoppndvlem6.w
    @23
    knoppndvlem6.c
    knoppndvlem6.n
    knoppndvlem4
    @32
    @0
    cli
    caddc
    @3
    cc0
    seqex
    cA
    cW
    fvex
    breldm
    syl
    isumsplit
    wph
    @13
    @5
    @8
    caddc
    wph
    @12
    @1
    @4
    vi
    wph
    @11
    cJ
    cc0
    cfz
    wph
    cJ
    c1
    wph
    cJ
    knoppndvlem6.j
    nn0cnd
    wph
    1cnd
    pncand
    oveq2d
    sumeq1d
    oveq1d
    3eqtrd
    wph
    @9
    @5
    cc0
    caddc
    co
    @5
    wph
    @8
    cc0
    @5
    caddc
    wph
    @8
    @7
    cc0
    vi
    csu
    #
    cc0
    wph
    @7
    @4
    cc0
    vi
    wph
    @2
    @7
    wcel
    #
    wa
    #
    @4
    cC
    @2
    cexp
    co
    #
    @19
    @2
    cexp
    co
    #
    cA
    cmul
    co
    #
    cT
    cfv
    #
    cmul
    co
    @36
    cc0
    cmul
    co
    cc0
    @35
    vy
    cA
    cC
    cT
    vn
    cF
    @2
    cN
    knoppndvlem6.f
    wph
    @31
    @34
    @23
    adantr
    wph
    @24
    @34
    @26
    @25
    @2
    @6
    eluznn0
    sylan
    #
    knoppcnlem1
    @35
    @39
    cc0
    @36
    cmul
    @35
    vx
    @38
    cT
    knoppndvlem6.t
    @35
    @38
    @37
    @20
    cmul
    co
    cz
    @35
    cA
    @20
    @37
    cmul
    @21
    @35
    knoppndvlem6.a
    a1i
    oveq2d
    @35
    @2
    cJ
    cM
    cN
    wph
    @28
    @34
    knoppndvlem6.n
    adantr
    @35
    @2
    @40
    nn0zd
    #
    wph
    cJ
    cz
    wcel
    #
    @34
    @22
    adantr
    #
    wph
    cM
    cz
    wcel
    @34
    knoppndvlem6.m
    adantr
    @35
    cJ
    @2
    clt
    wbr
    #
    @6
    @2
    cle
    wbr
    #
    @34
    @45
    wph
    @6
    @2
    eluzle
    adantl
    @35
    @42
    @2
    cz
    wcel
    #
    wa
    @44
    @45
    wb
    @35
    @42
    @46
    @43
    @41
    jca
    cJ
    @2
    zltp1le
    syl
    mpbird
    knoppndvlem2
    eqeltrd
    dnizeq0
    oveq2d
    @35
    @36
    @35
    cC
    @2
    wph
    cC
    cc
    wcel
    @34
    wph
    cC
    @30
    recnd
    adantr
    @40
    expcld
    mul01d
    3eqtrd
    sumeq2dv
    wph
    @7
    @7
    wss
    #
    @7
    cfn
    wcel
    #
    wo
    @33
    cc0
    wceq
    wph
    @47
    @48
    @47
    wph
    @7
    ssid
    a1i
    orcd
    @7
    vi
    @6
    sumz
    syl
    eqtrd
    oveq2d
    wph
    @5
    wph
    @5
    wph
    vx
    vy
    cA
    cC
    cT
    vi
    vn
    cF
    cJ
    cN
    knoppndvlem6.t
    knoppndvlem6.f
    @23
    @30
    knoppndvlem6.n
    knoppndvlem5
    recnd
    addid1d
    eqtrd
    eqtrd
end
