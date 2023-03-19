include "cn0.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfv.mm"
include "cdiv.mm"
include "cabs.mm"
include "cmpt.mm"
include "cmin.mm"
include "cli.mm"
include "wceq.mm"
include "cmul.mm"
include "cbcc.mm"
include "cc.mm"
include "adantr.mm"
include "simpr.mm"
include "bccp1k.mm"
include "cvv.mm"
include "a1i.mm"
include "oveq2d.mm"
include "1nn0.mm"
include "nn0addcld.mm"
include "ovexd.mm"
include "fvmptd.mm"
include "oveq1d.mm"
include "3eqtr4d.mm"
include "adantlr.mm"
include "eqcomd.mm"
include "bcccl.mm"
include "eqeltrd.mm"
include "nn0cnd.mm"
include "subcld.mm"
include "1cnd.mm"
include "addcld.mm"
include "cc0.mm"
include "wne.mm"
include "nn0p1nn.mm"
include "nnne0d.mm"
include "adantl.mm"
include "divcld.mm"
include "mulcld.mm"
include "cfz.mm"
include "elfznn0.mm"
include "con3i.mm"
include "ad2antlr.mm"
include "bcc0.mm"
include "necon3abid.mm"
include "mpbird.mm"
include "eqnetrd.mm"
include "divmuld.mm"
include "fveq2d.mm"
include "mpteq2dva.mm"
include "wbr.mm"
include "binomcxplemrat.mm"
include "eqbrtrd.mm"

theorem binomcxplemfrat
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  assume binomcxp.a: |- ( ph -> A e. RR+ )
  assume binomcxp.b: |- ( ph -> B e. RR )
  assume binomcxp.lt: |- ( ph -> ( abs ` B ) < ( abs ` A ) )
  assume binomcxp.c: |- ( ph -> C e. CC )
  assume binomcxplem.f: |- F = ( j e. NN0 |-> ( C _Cc j ) )

  disjoint j k
  disjoint j ph
  disjoint k ph
  disjoint C j
  disjoint C k
  assert |- ( ( ph /\ -. C e. NN0 ) -> ( k e. NN0 |-> ( abs ` ( ( F ` ( k + 1 ) ) / ( F ` k ) ) ) ) ~~> 1 )

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
    vk
    cn0
    cC
    @3
    cmin
    co
    #
    @4
    cdiv
    co
    #
    cabs
    cfv
    #
    cmpt
    #
    c1
    cli
    @2
    vk
    cn0
    @8
    @11
    @2
    @3
    cn0
    wcel
    #
    wa
    #
    @7
    @10
    cabs
    @14
    @7
    @10
    wceq
    @6
    @10
    cmul
    co
    #
    @5
    wceq
    @14
    @5
    @15
    wph
    @13
    @5
    @15
    wceq
    @1
    wph
    @13
    wa
    #
    cC
    @4
    cbcc
    co
    #
    cC
    @3
    cbcc
    co
    #
    @10
    cmul
    co
    @5
    @15
    @16
    cC
    @3
    wph
    cC
    cc
    wcel
    #
    @13
    binomcxp.c
    adantr
    #
    wph
    @13
    simpr
    #
    bccp1k
    @16
    vj
    @4
    cC
    vj
    cv
    #
    cbcc
    co
    #
    @17
    cn0
    cF
    cvv
    cF
    vj
    cn0
    @23
    cmpt
    wceq
    @16
    binomcxplem.f
    a1i
    #
    @16
    @22
    @4
    wceq
    #
    wa
    @22
    @4
    cC
    cbcc
    @16
    @25
    simpr
    oveq2d
    @16
    @3
    c1
    @21
    c1
    cn0
    wcel
    @16
    1nn0
    a1i
    nn0addcld
    @16
    cC
    @4
    cbcc
    ovexd
    fvmptd
    @16
    @6
    @18
    @10
    cmul
    @16
    vj
    @3
    @23
    @18
    cn0
    cF
    cvv
    @24
    @16
    @22
    @3
    wceq
    #
    wa
    @22
    @3
    cC
    cbcc
    @16
    @26
    simpr
    oveq2d
    @21
    @16
    cC
    @3
    cbcc
    ovexd
    fvmptd
    #
    oveq1d
    3eqtr4d
    adantlr
    #
    eqcomd
    @14
    @5
    @6
    @10
    @14
    @5
    @15
    cc
    @28
    @14
    @6
    @10
    wph
    @13
    @6
    cc
    wcel
    @1
    @16
    @6
    @18
    cc
    @27
    @16
    cC
    @3
    @20
    @21
    bcccl
    eqeltrd
    adantlr
    #
    @14
    @9
    @4
    @14
    cC
    @3
    wph
    @13
    @19
    @1
    @20
    adantlr
    #
    @14
    @3
    @2
    @13
    simpr
    #
    nn0cnd
    #
    subcld
    @14
    @3
    c1
    @32
    @14
    1cnd
    addcld
    @13
    @4
    cc0
    wne
    @2
    @13
    @4
    @3
    nn0p1nn
    nnne0d
    adantl
    divcld
    #
    mulcld
    eqeltrd
    @29
    @33
    @14
    @6
    @18
    cc0
    wph
    @13
    @6
    @18
    wceq
    @1
    @27
    adantlr
    @14
    @18
    cc0
    wne
    cC
    cc0
    @3
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
    @36
    wph
    @13
    @35
    @0
    cC
    @34
    elfznn0
    con3i
    ad2antlr
    @14
    @35
    @18
    cc0
    @14
    cC
    @3
    @30
    @31
    bcc0
    necon3abid
    mpbird
    eqnetrd
    divmuld
    mpbird
    fveq2d
    mpteq2dva
    wph
    @12
    c1
    cli
    wbr
    @1
    wph
    cA
    cB
    cC
    vk
    binomcxp.a
    binomcxp.b
    binomcxp.lt
    binomcxp.c
    binomcxplemrat
    adantr
    eqbrtrd
end
