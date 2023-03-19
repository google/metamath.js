include "cn0.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cdiv.mm"
include "cabs.mm"
include "cfv.mm"
include "cmpt.mm"
include "cneg.mm"
include "cli.mm"
include "cc0.mm"
include "cvv.mm"
include "nn0uz.mm"
include "cof.mm"
include "0zd.mm"
include "cc.mm"
include "wcel.mm"
include "peano2cn.mm"
include "syl.mm"
include "1zzd.mm"
include "nn0ex.mm"
include "mptex.mm"
include "a1i.mm"
include "wa.mm"
include "eqidd.mm"
include "wceq.mm"
include "simpr.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "ovexd.mm"
include "fvmptd.mm"
include "divcnvshft.mm"
include "wbr.mm"
include "csn.mm"
include "cxp.mm"
include "nn0cn.mm"
include "1cnd.mm"
include "addcld.mm"
include "nn0p1nn.mm"
include "nnne0d.mm"
include "dividd.mm"
include "mpteq2ia.mm"
include "fconstmpt.mm"
include "eqtr4i.mm"
include "cz.mm"
include "ax-1cn.mm"
include "0z.mm"
include "cuz.mm"
include "eqimss2i.mm"
include "climconst2.mm"
include "mp2an.mm"
include "eqbrtri.mm"
include "adantr.mm"
include "nn0cnd.mm"
include "wne.mm"
include "adantl.mm"
include "divcld.mm"
include "eqeltrd.mm"
include "oveq12d.mm"
include "wfn.mm"
include "ovex.mm"
include "eqid.mm"
include "fnmpti.mm"
include "inidm.mm"
include "ofval.mm"
include "climsub.mm"
include "offval2.mm"
include "divsubdird.mm"
include "pnpcan2d.mm"
include "eqtr3d.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "df-neg.mm"
include "eqcomi.mm"
include "3brtr3d.mm"
include "oveq2.mm"
include "oveq1.mm"
include "subcld.mm"
include "fveq2d.mm"
include "fvexd.mm"
include "eqtr4d.mm"
include "climabs.mm"
include "absnegi.mm"
include "abs1.mm"
include "eqtri.mm"
include "syl6breq.mm"

theorem binomcxplemrat
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vx: setvar x
  assume binomcxp.a: |- ( ph -> A e. RR+ )
  assume binomcxp.b: |- ( ph -> B e. RR )
  assume binomcxp.lt: |- ( ph -> ( abs ` B ) < ( abs ` A ) )
  assume binomcxp.c: |- ( ph -> C e. CC )

  disjoint k ph
  disjoint C k
  disjoint k x
  disjoint ph x
  disjoint C x
  assert |- ( ph -> ( k e. NN0 |-> ( abs ` ( ( C - k ) / ( k + 1 ) ) ) ) ~~> 1 )

  proof
    wph
    vk
    cn0
    cC
    vk
    cv
    #
    cmin
    co
    #
    @0
    c1
    caddc
    co
    #
    cdiv
    co
    #
    cabs
    cfv
    #
    cmpt
    #
    c1
    cneg
    #
    cabs
    cfv
    #
    c1
    cli
    wph
    @6
    vx
    vk
    cn0
    @3
    cmpt
    #
    @5
    cc0
    cvv
    cn0
    nn0uz
    wph
    vk
    cn0
    cC
    c1
    caddc
    co
    #
    @2
    cdiv
    co
    #
    cmpt
    #
    vk
    cn0
    @2
    @2
    cdiv
    co
    #
    cmpt
    #
    cmin
    cof
    #
    co
    #
    cc0
    c1
    cmin
    co
    #
    @8
    @6
    cli
    wph
    cc0
    c1
    vx
    @11
    @13
    @15
    cc0
    cvv
    cn0
    nn0uz
    wph
    0zd
    #
    wph
    @9
    c1
    vx
    @11
    cc0
    cvv
    cn0
    nn0uz
    @17
    wph
    cC
    cc
    wcel
    #
    @9
    cc
    wcel
    #
    binomcxp.c
    cC
    peano2cn
    syl
    #
    wph
    1zzd
    @11
    cvv
    wcel
    wph
    vk
    cn0
    @10
    nn0ex
    mptex
    a1i
    wph
    vx
    cv
    #
    cn0
    wcel
    #
    wa
    #
    vk
    @21
    @10
    @9
    @21
    c1
    caddc
    co
    #
    cdiv
    co
    #
    cn0
    @11
    cvv
    @23
    @11
    eqidd
    @23
    @0
    @21
    wceq
    #
    wa
    #
    @2
    @24
    @9
    cdiv
    @27
    @0
    @21
    c1
    caddc
    @23
    @26
    simpr
    oveq1d
    #
    oveq2d
    wph
    @22
    simpr
    #
    @23
    @9
    @24
    cdiv
    ovexd
    fvmptd
    #
    divcnvshft
    wph
    @11
    @13
    @14
    ovexd
    @13
    c1
    cli
    wbr
    wph
    @13
    cn0
    c1
    csn
    cxp
    #
    c1
    cli
    @13
    vk
    cn0
    c1
    cmpt
    @31
    vk
    cn0
    @12
    c1
    @0
    cn0
    wcel
    #
    @2
    @32
    @0
    c1
    @0
    nn0cn
    #
    @32
    1cnd
    addcld
    #
    @32
    @2
    @0
    nn0p1nn
    nnne0d
    #
    dividd
    mpteq2ia
    vk
    cn0
    c1
    fconstmpt
    eqtr4i
    c1
    cc
    wcel
    cc0
    cz
    wcel
    @31
    c1
    cli
    wbr
    ax-1cn
    0z
    c1
    cc0
    cn0
    cn0
    cc0
    cuz
    cfv
    nn0uz
    eqimss2i
    nn0ex
    climconst2
    mp2an
    eqbrtri
    a1i
    @23
    @21
    @11
    cfv
    #
    @25
    cc
    @30
    @23
    @9
    @24
    @23
    cC
    c1
    wph
    @18
    @22
    binomcxp.c
    adantr
    #
    @23
    1cnd
    #
    addcld
    @23
    @21
    c1
    @23
    @21
    @29
    nn0cnd
    #
    @38
    addcld
    #
    @22
    @24
    cc0
    wne
    wph
    @22
    @24
    @21
    nn0p1nn
    nnne0d
    adantl
    #
    divcld
    eqeltrd
    @23
    @21
    @13
    cfv
    #
    @24
    @24
    cdiv
    co
    #
    cc
    @23
    vk
    @21
    @12
    @43
    cn0
    @13
    cvv
    @23
    @13
    eqidd
    @27
    @2
    @24
    @2
    @24
    cdiv
    @28
    @28
    oveq12d
    @29
    @23
    @24
    @24
    cdiv
    ovexd
    fvmptd
    @23
    @24
    @24
    @40
    @40
    @41
    divcld
    eqeltrd
    wph
    cn0
    cn0
    @36
    @42
    cmin
    cn0
    @11
    @13
    cvv
    cvv
    @21
    @11
    cn0
    wfn
    wph
    vk
    cn0
    @10
    @11
    @9
    @2
    cdiv
    ovex
    @11
    eqid
    fnmpti
    a1i
    @13
    cn0
    wfn
    wph
    vk
    cn0
    @12
    @13
    @2
    @2
    cdiv
    ovex
    @13
    eqid
    fnmpti
    a1i
    cn0
    cvv
    wcel
    wph
    nn0ex
    a1i
    #
    @44
    cn0
    inidm
    @23
    @36
    eqidd
    @23
    @42
    eqidd
    ofval
    climsub
    wph
    @15
    vk
    cn0
    @10
    @12
    cmin
    co
    #
    cmpt
    @8
    wph
    vk
    cn0
    @10
    @12
    cmin
    @11
    @13
    cvv
    cvv
    cvv
    @44
    wph
    @32
    wa
    #
    @9
    @2
    cdiv
    ovexd
    @46
    @2
    @2
    cdiv
    ovexd
    wph
    @11
    eqidd
    wph
    @13
    eqidd
    offval2
    wph
    vk
    cn0
    @45
    @3
    @46
    @9
    @2
    cmin
    co
    #
    @2
    cdiv
    co
    @45
    @3
    @46
    @9
    @2
    @2
    wph
    @19
    @32
    @20
    adantr
    @32
    @2
    cc
    wcel
    wph
    @34
    adantl
    #
    @48
    @32
    @2
    cc0
    wne
    wph
    @35
    adantl
    divsubdird
    @46
    @47
    @1
    @2
    cdiv
    @46
    cC
    @0
    c1
    wph
    @18
    @32
    binomcxp.c
    adantr
    @32
    @0
    cc
    wcel
    wph
    @33
    adantl
    @46
    1cnd
    pnpcan2d
    oveq1d
    eqtr3d
    mpteq2dva
    eqtrd
    @16
    @6
    wceq
    wph
    @6
    @16
    c1
    df-neg
    eqcomi
    a1i
    3brtr3d
    @5
    cvv
    wcel
    wph
    vk
    cn0
    @4
    nn0ex
    mptex
    a1i
    @17
    @23
    @21
    @8
    cfv
    #
    cC
    @21
    cmin
    co
    #
    @24
    cdiv
    co
    #
    cc
    @23
    vk
    @21
    @3
    @51
    cn0
    @8
    cvv
    @23
    @8
    eqidd
    @26
    @3
    @51
    wceq
    @23
    @26
    @1
    @50
    @2
    @24
    cdiv
    @0
    @21
    cC
    cmin
    oveq2
    @0
    @21
    c1
    caddc
    oveq1
    oveq12d
    #
    adantl
    @29
    @23
    @50
    @24
    cdiv
    ovexd
    fvmptd
    #
    @23
    @50
    @24
    @23
    cC
    @21
    @37
    @39
    subcld
    @40
    @41
    divcld
    eqeltrd
    @23
    @21
    @5
    cfv
    @51
    cabs
    cfv
    #
    @49
    cabs
    cfv
    @23
    vk
    @21
    @4
    @54
    cn0
    @5
    cvv
    @23
    @5
    eqidd
    @26
    @4
    @54
    wceq
    @23
    @26
    @3
    @51
    cabs
    @52
    fveq2d
    adantl
    @29
    @23
    @51
    cabs
    fvexd
    fvmptd
    @23
    @49
    @51
    cabs
    @53
    fveq2d
    eqtr4d
    climabs
    @7
    c1
    cabs
    cfv
    c1
    c1
    ax-1cn
    absnegi
    abs1
    eqtri
    syl6breq
end
