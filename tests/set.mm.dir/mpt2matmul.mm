include "co.mm"
include "cotp.mm"
include "cmmul.mm"
include "cv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "cfn.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "cmulr.mm"
include "cfv.mm"
include "eqid.mm"
include "matmulr.mm"
include "syl6eqr.mm"
include "oveqd.mm"
include "eqcomd.mm"
include "syl2anc.mm"
include "cbs.mm"
include "cxp.mm"
include "cmap.mm"
include "w3a.mm"
include "syl6eleq.mm"
include "matbas2d.mm"
include "syl5eqel.mm"
include "matbas2.mm"
include "eleqtrrd.mm"
include "mamuval.mm"
include "a1i.mm"
include "weq.mm"
include "wi.mm"
include "equcom.mm"
include "anbi12i.mm"
include "sylan2b.mm"
include "ex.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "imp.mm"
include "simpl2.mm"
include "simpr.mm"
include "simpl1.mm"
include "syl3anc.mm"
include "ovmpt2d.mm"
include "equcomi.mm"
include "anim12i.mm"
include "sylan2.mm"
include "simpl3.mm"
include "oveq12d.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "mpt2eq3dva.mm"
include "3eqtrd.mm"

theorem mpt2matmul
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let cU: class U
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let cE: class E
  let cF: class F
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vl: setvar l
  assume mpt2matmul.a: |- A = ( N Mat R )
  assume mpt2matmul.b: |- B = ( Base ` R )
  assume mpt2matmul.m: |- .X. = ( .r ` A )
  assume mpt2matmul.t: |- .x. = ( .r ` R )
  assume mpt2matmul.r: |- ( ph -> R e. V )
  assume mpt2matmul.n: |- ( ph -> N e. Fin )
  assume mpt2matmul.x: |- X = ( i e. N , j e. N |-> C )
  assume mpt2matmul.y: |- Y = ( i e. N , j e. N |-> E )
  assume mpt2matmul.c: |- ( ( ph /\ i e. N /\ j e. N ) -> C e. B )
  assume mpt2matmul.e: |- ( ( ph /\ i e. N /\ j e. N ) -> E e. B )
  assume mpt2matmul.d: |- ( ( ph /\ ( k = i /\ m = j ) ) -> D = C )
  assume mpt2matmul.f: |- ( ( ph /\ ( m = i /\ l = j ) ) -> F = E )
  assume mpt2matmul.1: |- ( ( ph /\ k e. N /\ m e. N ) -> D e. U )
  assume mpt2matmul.2: |- ( ( ph /\ m e. N /\ l e. N ) -> F e. W )

  disjoint D i
  disjoint D j
  disjoint i j
  disjoint F i
  disjoint F j
  disjoint N i
  disjoint N j
  disjoint N k
  disjoint N l
  disjoint N m
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint j k
  disjoint j l
  disjoint j m
  disjoint k l
  disjoint k m
  disjoint l m
  disjoint R i
  disjoint R j
  disjoint R k
  disjoint R l
  disjoint R m
  disjoint X k
  disjoint X l
  disjoint X m
  disjoint Y k
  disjoint Y l
  disjoint Y m
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint l ph
  disjoint m ph
  disjoint .x. k
  disjoint .x. l
  assert |- ( ph -> ( X .X. Y ) = ( k e. N , l e. N |-> ( R gsum ( m e. N |-> ( D .x. F ) ) ) ) )

  proof
    wph
    cX
    cY
    c.xp
    co
    #
    cX
    cY
    cR
    cN
    cN
    cN
    cotp
    cmmul
    co
    #
    co
    #
    vk
    vl
    cN
    cN
    cR
    vm
    cN
    vk
    cv
    #
    vm
    cv
    #
    cX
    co
    #
    @4
    vl
    cv
    #
    cY
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt2
    vk
    vl
    cN
    cN
    cR
    vm
    cN
    cD
    cF
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt2
    wph
    cN
    cfn
    wcel
    #
    cR
    cV
    wcel
    #
    @0
    @2
    wceq
    mpt2matmul.n
    mpt2matmul.r
    @14
    @15
    wa
    #
    @2
    @0
    @16
    @1
    c.xp
    cX
    cY
    @16
    @1
    cA
    cmulr
    cfv
    c.xp
    cA
    cR
    @1
    cN
    cV
    mpt2matmul.a
    @1
    eqid
    #
    matmulr
    mpt2matmul.m
    syl6eqr
    oveqd
    eqcomd
    syl2anc
    wph
    cR
    cbs
    cfv
    #
    cN
    cR
    c.x
    vk
    vm
    vl
    @1
    cN
    cN
    cV
    cX
    cY
    @17
    @18
    eqid
    #
    mpt2matmul.t
    mpt2matmul.r
    mpt2matmul.n
    mpt2matmul.n
    mpt2matmul.n
    wph
    cX
    cA
    cbs
    cfv
    #
    @18
    cN
    cN
    cxp
    cmap
    co
    #
    wph
    cX
    vi
    vj
    cN
    cN
    cC
    cmpt2
    #
    @20
    mpt2matmul.x
    wph
    vi
    vj
    cA
    @20
    cC
    cR
    @18
    cN
    cV
    mpt2matmul.a
    @19
    @20
    eqid
    #
    mpt2matmul.n
    mpt2matmul.r
    wph
    vi
    cv
    cN
    wcel
    vj
    cv
    cN
    wcel
    w3a
    #
    cC
    cB
    @18
    mpt2matmul.c
    mpt2matmul.b
    syl6eleq
    matbas2d
    syl5eqel
    wph
    @14
    @15
    @21
    @20
    wceq
    mpt2matmul.n
    mpt2matmul.r
    cA
    cR
    @18
    cN
    cV
    mpt2matmul.a
    @19
    matbas2
    syl2anc
    #
    eleqtrrd
    wph
    cY
    @20
    @21
    wph
    cY
    vi
    vj
    cN
    cN
    cE
    cmpt2
    #
    @20
    mpt2matmul.y
    wph
    vi
    vj
    cA
    @20
    cE
    cR
    @18
    cN
    cV
    mpt2matmul.a
    @19
    @23
    mpt2matmul.n
    mpt2matmul.r
    @24
    cE
    cB
    @18
    mpt2matmul.e
    mpt2matmul.b
    syl6eleq
    matbas2d
    syl5eqel
    @25
    eleqtrrd
    mamuval
    wph
    vk
    vl
    cN
    cN
    @10
    @13
    wph
    @3
    cN
    wcel
    #
    @6
    cN
    wcel
    #
    w3a
    #
    @9
    @12
    cR
    cgsu
    @29
    vm
    cN
    @8
    @11
    @29
    @4
    cN
    wcel
    #
    wa
    #
    @5
    cD
    @7
    cF
    c.x
    @31
    vi
    vj
    @3
    @4
    cN
    cN
    cC
    cD
    cX
    cU
    cX
    @22
    wceq
    @31
    mpt2matmul.x
    a1i
    @31
    vi
    vk
    weq
    #
    vj
    vm
    weq
    #
    wa
    #
    cC
    cD
    wceq
    #
    @29
    @34
    @35
    wi
    #
    @30
    wph
    @27
    @36
    @28
    wph
    @34
    @35
    wph
    @34
    wa
    cD
    cC
    @34
    wph
    vk
    vi
    weq
    #
    vm
    vj
    weq
    #
    wa
    cD
    cC
    wceq
    @32
    @37
    @33
    @38
    vi
    vk
    equcom
    vj
    vm
    equcom
    anbi12i
    mpt2matmul.d
    sylan2b
    eqcomd
    ex
    3ad2ant1
    adantr
    imp
    wph
    @27
    @28
    @30
    simpl2
    #
    @29
    @30
    simpr
    #
    @31
    wph
    @27
    @30
    cD
    cU
    wcel
    wph
    @27
    @28
    @30
    simpl1
    #
    @39
    @40
    mpt2matmul.1
    syl3anc
    ovmpt2d
    @31
    vi
    vj
    @4
    @6
    cN
    cN
    cE
    cF
    cY
    cW
    cY
    @26
    wceq
    @31
    mpt2matmul.y
    a1i
    @31
    vi
    vm
    weq
    #
    vj
    vl
    weq
    #
    wa
    #
    wa
    cF
    cE
    @31
    @44
    cF
    cE
    wceq
    #
    @29
    @44
    @45
    wi
    #
    @30
    wph
    @27
    @46
    @28
    wph
    @44
    @45
    @44
    wph
    vm
    vi
    weq
    #
    vl
    vj
    weq
    #
    wa
    @45
    @42
    @47
    @43
    @48
    vi
    vm
    equcomi
    vj
    vl
    equcomi
    anim12i
    mpt2matmul.f
    sylan2
    ex
    3ad2ant1
    adantr
    imp
    eqcomd
    @40
    wph
    @27
    @28
    @30
    simpl3
    #
    @31
    wph
    @30
    @28
    cF
    cW
    wcel
    @41
    @40
    @49
    mpt2matmul.2
    syl3anc
    ovmpt2d
    oveq12d
    mpteq2dva
    oveq2d
    mpt2eq3dva
    3eqtrd
end
