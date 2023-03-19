include "caddc.mm"
include "cseq.mm"
include "cuz.mm"
include "cfv.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cexp.mm"
include "cmul.mm"
include "cmpt.mm"
include "c1.mm"
include "cdiv.mm"
include "cli.mm"
include "wceq.mm"
include "seqeq3.mm"
include "ax-mp.mm"
include "wbr.mm"
include "cneg.mm"
include "cshi.mm"
include "cc0.mm"
include "cn0.mm"
include "nn0uz.mm"
include "0zd.mm"
include "wcel.mm"
include "oveq2.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "geolim.mm"
include "wa.mm"
include "cc.mm"
include "expcl.mm"
include "sylan.mm"
include "eqeltrd.mm"
include "zcnd.mm"
include "nn0cn.mm"
include "fvex.mm"
include "mptex.mm"
include "shftval4.mm"
include "syl2an.mm"
include "cz.mm"
include "uzid.mm"
include "syl.mm"
include "uzaddcl.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "pncan2.mm"
include "eqtr4d.mm"
include "3eqtrd.mm"
include "isermulc2.mm"
include "negidd.mm"
include "seqeq1d.mm"
include "ax-1cn.mm"
include "subcl.mm"
include "sylancr.mm"
include "wne.mm"
include "cabs.mm"
include "abs1.mm"
include "a1i.mm"
include "abscld.mm"
include "gtned.mm"
include "eqnetrd.mm"
include "fveq2.mm"
include "necon3i.mm"
include "wb.mm"
include "subeq0.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "divrecd.mm"
include "3brtr4d.mm"
include "znegcld.mm"
include "isershft.mm"
include "syl2anc.mm"
include "syl5eqbr.mm"

theorem geolim3
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cF: class F
  let va: setvar a
  assume geolim3.a: |- ( ph -> A e. ZZ )
  assume geolim3.b1: |- ( ph -> B e. CC )
  assume geolim3.b2: |- ( ph -> ( abs ` B ) < 1 )
  assume geolim3.c: |- ( ph -> C e. CC )
  assume geolim3.f: |- F = ( k e. ( ZZ>= ` A ) |-> ( C x. ( B ^ ( k - A ) ) ) )

  disjoint k ph
  disjoint A k
  disjoint B k
  disjoint C k
  disjoint a ph
  disjoint a k
  disjoint A a
  disjoint B a
  disjoint C a
  disjoint F a
  assert |- ( ph -> seq A ( + , F ) ~~> ( C / ( 1 - B ) ) )

  proof
    wph
    caddc
    cF
    cA
    cseq
    #
    caddc
    vk
    cA
    cuz
    cfv
    #
    cC
    cB
    vk
    cv
    #
    cA
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    cA
    cseq
    #
    cC
    c1
    cB
    cmin
    co
    #
    cdiv
    co
    #
    cli
    cF
    @6
    wceq
    @0
    @7
    wceq
    geolim3.f
    caddc
    cF
    @6
    cA
    seqeq3
    ax-mp
    wph
    @7
    @9
    cli
    wbr
    #
    caddc
    @6
    cA
    cneg
    #
    cshi
    co
    #
    cA
    @11
    caddc
    co
    #
    cseq
    #
    @9
    cli
    wbr
    #
    wph
    caddc
    @12
    cc0
    cseq
    cC
    c1
    @8
    cdiv
    co
    #
    cmul
    co
    @14
    @9
    cli
    wph
    @16
    cC
    va
    vk
    cn0
    cB
    @2
    cexp
    co
    #
    cmpt
    #
    @12
    cc0
    cn0
    nn0uz
    wph
    0zd
    geolim3.c
    wph
    cB
    va
    @18
    geolim3.b1
    geolim3.b2
    va
    cv
    #
    cn0
    wcel
    #
    @19
    @18
    cfv
    #
    cB
    @19
    cexp
    co
    #
    wceq
    wph
    vk
    @19
    @17
    @22
    cn0
    @18
    @2
    @19
    cB
    cexp
    oveq2
    @18
    eqid
    cB
    @19
    cexp
    ovex
    fvmpt
    adantl
    #
    geolim
    wph
    @20
    wa
    #
    @21
    @22
    cc
    @23
    wph
    cB
    cc
    wcel
    #
    @20
    @22
    cc
    wcel
    geolim3.b1
    cB
    @19
    expcl
    sylan
    eqeltrd
    @24
    @19
    @12
    cfv
    #
    cA
    @19
    caddc
    co
    #
    @6
    cfv
    #
    cC
    cB
    @27
    cA
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    cC
    @21
    cmul
    co
    wph
    cA
    cc
    wcel
    #
    @19
    cc
    wcel
    #
    @26
    @28
    wceq
    @20
    wph
    cA
    geolim3.a
    zcnd
    #
    @19
    nn0cn
    #
    cA
    @19
    @6
    vk
    @1
    @5
    cA
    cuz
    fvex
    mptex
    #
    shftval4
    syl2an
    @24
    @27
    @1
    wcel
    #
    @28
    @31
    wceq
    wph
    cA
    @1
    wcel
    #
    @20
    @37
    wph
    cA
    cz
    wcel
    #
    @38
    geolim3.a
    cA
    uzid
    syl
    @19
    cA
    cA
    uzaddcl
    sylan
    vk
    @27
    @5
    @31
    @1
    @6
    @2
    @27
    wceq
    #
    @4
    @30
    cC
    cmul
    @40
    @3
    @29
    cB
    cexp
    @2
    @27
    cA
    cmin
    oveq1
    oveq2d
    oveq2d
    @6
    eqid
    cC
    @30
    cmul
    ovex
    fvmpt
    syl
    @24
    @30
    @21
    cC
    cmul
    @24
    @30
    @22
    @21
    @24
    @29
    @19
    cB
    cexp
    wph
    @32
    @33
    @29
    @19
    wceq
    @20
    @34
    @35
    cA
    @19
    pncan2
    syl2an
    oveq2d
    @23
    eqtr4d
    oveq2d
    3eqtrd
    isermulc2
    wph
    @13
    cc0
    caddc
    @12
    wph
    cA
    @34
    negidd
    seqeq1d
    wph
    cC
    @8
    geolim3.c
    wph
    c1
    cc
    wcel
    #
    @25
    @8
    cc
    wcel
    ax-1cn
    geolim3.b1
    c1
    cB
    subcl
    sylancr
    wph
    @8
    cc0
    wne
    c1
    cB
    wne
    #
    wph
    c1
    cabs
    cfv
    #
    cB
    cabs
    cfv
    #
    wne
    @42
    wph
    @43
    c1
    @44
    @43
    c1
    wceq
    wph
    abs1
    a1i
    wph
    @44
    c1
    wph
    cB
    geolim3.b1
    abscld
    geolim3.b2
    gtned
    eqnetrd
    c1
    cB
    @43
    @44
    c1
    cB
    cabs
    fveq2
    necon3i
    syl
    wph
    @8
    cc0
    c1
    cB
    wph
    @41
    @25
    @8
    cc0
    wceq
    c1
    cB
    wceq
    wb
    ax-1cn
    geolim3.b1
    c1
    cB
    subeq0
    sylancr
    necon3bid
    mpbird
    divrecd
    3brtr4d
    wph
    @39
    @11
    cz
    wcel
    @10
    @15
    wb
    geolim3.a
    wph
    cA
    geolim3.a
    znegcld
    @9
    caddc
    @6
    cA
    @11
    @36
    isershft
    syl2anc
    mpbird
    syl5eqbr
end
