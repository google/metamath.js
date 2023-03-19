include "cn0.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cv.mm"
include "caddc.mm"
include "cfv.mm"
include "cabs.mm"
include "cmpt.mm"
include "cc0.mm"
include "cc.mm"
include "cexp.mm"
include "cmul.mm"
include "wceq.mm"
include "simpl.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "mpteq2dva.mm"
include "fveq2.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "cbvmptv.mm"
include "syl6eq.mm"
include "eqtri.mm"
include "cbcc.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "bcccl.mm"
include "fmptd.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "nn0uz.mm"
include "0nn0.mm"
include "a1i.mm"
include "cvv.mm"
include "ovexd.mm"
include "fvmptd.mm"
include "wne.mm"
include "cmin.mm"
include "cfz.mm"
include "elfznn0.mm"
include "con3i.mm"
include "ad2antlr.mm"
include "wb.mm"
include "adantr.mm"
include "bcc0.mm"
include "necon3abid.mm"
include "adantlr.mm"
include "mpbird.mm"
include "eqnetrd.mm"
include "binomcxplemfrat.mm"
include "ax-1ne0.mm"
include "radcnvrat.mm"
include "1div1e1.mm"

theorem binomcxplemradcnv
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let vr: setvar r
  let vb: setvar b
  let vi: setvar i
  let vx: setvar x
  let vy: setvar y
  assume binomcxp.a: |- ( ph -> A e. RR+ )
  assume binomcxp.b: |- ( ph -> B e. RR )
  assume binomcxp.lt: |- ( ph -> ( abs ` B ) < ( abs ` A ) )
  assume binomcxp.c: |- ( ph -> C e. CC )
  assume binomcxplem.f: |- F = ( j e. NN0 |-> ( C _Cc j ) )
  assume binomcxplem.s: |- S = ( b e. CC |-> ( k e. NN0 |-> ( ( F ` k ) x. ( b ^ k ) ) ) )
  assume binomcxplem.r: |- R = sup ( { r e. RR | seq 0 ( + , ( S ` r ) ) e. dom ~~> } , RR* , < )

  disjoint C k
  disjoint b k
  disjoint F b
  disjoint F k
  disjoint j k
  disjoint j ph
  disjoint k ph
  disjoint C j
  disjoint S r
  disjoint i k
  disjoint i x
  disjoint i y
  disjoint C i
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint b x
  disjoint b y
  disjoint F x
  disjoint F y
  disjoint F i
  disjoint i j
  disjoint i ph
  disjoint i r
  disjoint S i
  disjoint r x
  disjoint S x
  disjoint S y
  disjoint ph x
  disjoint ph y
  assert |- ( ( ph /\ -. C e. NN0 ) -> R = 1 )

  proof
    wph
    cC
    cn0
    wcel
    #
    wn
    #
    wa
    #
    cR
    c1
    c1
    cdiv
    co
    c1
    @2
    vx
    cF
    vk
    cn0
    vk
    cv
    #
    c1
    caddc
    co
    #
    cF
    cfv
    #
    @3
    cF
    cfv
    #
    cdiv
    co
    #
    cabs
    cfv
    #
    cmpt
    cR
    vi
    vy
    cS
    c1
    cc0
    cn0
    vr
    cS
    vb
    cc
    vk
    cn0
    @6
    vb
    cv
    #
    @3
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    cmpt
    vx
    cc
    vy
    cn0
    vy
    cv
    #
    cF
    cfv
    #
    vx
    cv
    #
    @13
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    cmpt
    binomcxplem.s
    vb
    vx
    cc
    @12
    @18
    @9
    @15
    wceq
    #
    @12
    vk
    cn0
    @6
    @15
    @3
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    @18
    @19
    vk
    cn0
    @11
    @21
    @19
    @3
    cn0
    wcel
    #
    wa
    #
    @10
    @20
    @6
    cmul
    @23
    @9
    @15
    @3
    cexp
    @19
    @22
    simpl
    oveq1d
    oveq2d
    mpteq2dva
    vk
    vy
    cn0
    @21
    @17
    @3
    @13
    wceq
    @6
    @14
    @20
    @16
    cmul
    @3
    @13
    cF
    fveq2
    @3
    @13
    @15
    cexp
    oveq2
    oveq12d
    cbvmptv
    syl6eq
    cbvmptv
    eqtri
    @2
    vj
    cn0
    cC
    vj
    cv
    #
    cbcc
    co
    #
    cc
    cF
    @2
    @24
    cn0
    wcel
    #
    wa
    cC
    @24
    wph
    cC
    cc
    wcel
    #
    @1
    @26
    binomcxp.c
    ad2antrr
    @2
    @26
    simpr
    bcccl
    binomcxplem.f
    fmptd
    binomcxplem.r
    vk
    vi
    cn0
    @8
    vi
    cv
    #
    c1
    caddc
    co
    #
    cF
    cfv
    #
    @28
    cF
    cfv
    #
    cdiv
    co
    #
    cabs
    cfv
    @3
    @28
    wceq
    #
    @7
    @32
    cabs
    @33
    @5
    @30
    @6
    @31
    cdiv
    @33
    @4
    @29
    cF
    @3
    @28
    c1
    caddc
    oveq1
    fveq2d
    @3
    @28
    cF
    fveq2
    oveq12d
    fveq2d
    cbvmptv
    nn0uz
    cc0
    cn0
    wcel
    @2
    0nn0
    a1i
    @2
    @28
    cn0
    wcel
    #
    wa
    #
    @31
    cC
    @28
    cbcc
    co
    #
    cc0
    @35
    vj
    @28
    @25
    @36
    cn0
    cF
    cvv
    cF
    vj
    cn0
    @25
    cmpt
    wceq
    @35
    binomcxplem.f
    a1i
    @35
    @24
    @28
    wceq
    #
    wa
    @24
    @28
    cC
    cbcc
    @35
    @37
    simpr
    oveq2d
    @2
    @34
    simpr
    @35
    cC
    @28
    cbcc
    ovexd
    fvmptd
    @35
    @36
    cc0
    wne
    #
    cC
    cc0
    @28
    c1
    cmin
    co
    #
    cfz
    co
    wcel
    #
    wn
    #
    @1
    @41
    wph
    @34
    @40
    @0
    cC
    @39
    elfznn0
    con3i
    ad2antlr
    wph
    @34
    @38
    @41
    wb
    @1
    wph
    @34
    wa
    #
    @40
    @36
    cc0
    @42
    cC
    @28
    wph
    @27
    @34
    binomcxp.c
    adantr
    wph
    @34
    simpr
    bcc0
    necon3abid
    adantlr
    mpbird
    eqnetrd
    wph
    cA
    cB
    cC
    vj
    vk
    cF
    binomcxp.a
    binomcxp.b
    binomcxp.lt
    binomcxp.c
    binomcxplem.f
    binomcxplemfrat
    c1
    cc0
    wne
    @2
    ax-1ne0
    a1i
    radcnvrat
    1div1e1
    syl6eq
end
