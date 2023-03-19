include "c1.mm"
include "cli.mm"
include "wbr.mm"
include "cz.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "cdiv.mm"
include "cmpt.mm"
include "cn.mm"
include "cc0.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "nncn.mm"
include "adantl.mm"
include "zcnd.mm"
include "subcld.mm"
include "adantr.mm"
include "wne.mm"
include "nnne0.mm"
include "divdird.mm"
include "dividd.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "cvv.mm"
include "nnuz.mm"
include "1zzd.mm"
include "divcnv.mm"
include "syl.mm"
include "1cnd.mm"
include "nnex.mm"
include "mptex.mm"
include "a1i.mm"
include "divcld.mm"
include "eqid.mm"
include "fmptd.mm"
include "ffvelrnda.mm"
include "cfv.mm"
include "wceq.mm"
include "weq.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "eqtr4d.mm"
include "climaddc2.mm"
include "eqbrtrd.mm"
include "cuz.mm"
include "cres.mm"
include "wss.mm"
include "nnssz.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "reseq2i.mm"
include "eqtr3i.mm"
include "1p0e1.mm"
include "breq12i.mm"
include "wb.mm"
include "1z.mm"
include "zex.mm"
include "climres.mm"
include "mp2an.mm"
include "bitri.mm"
include "sylib.mm"
include "eluzelz.mm"
include "eleq2s.mm"
include "ppncand.mm"
include "zaddcld.mm"
include "oveq1.mm"
include "id.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "climshft2.mm"
include "mpbird.mm"

theorem divcnvlin
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vm: setvar m
  assume divcnvlin.1: |- Z = ( ZZ>= ` M )
  assume divcnvlin.2: |- ( ph -> M e. ZZ )
  assume divcnvlin.3: |- ( ph -> A e. CC )
  assume divcnvlin.4: |- ( ph -> B e. ZZ )
  assume divcnvlin.5: |- ( ph -> F e. V )
  assume divcnvlin.6: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = ( ( k + A ) / ( k + B ) ) )

  disjoint A k
  disjoint B k
  disjoint F k
  disjoint k ph
  disjoint M k
  disjoint Z k
  disjoint A m
  disjoint B m
  disjoint k m
  disjoint m ph
  assert |- ( ph -> F ~~> 1 )

  proof
    wph
    cF
    c1
    cli
    wbr
    vm
    cz
    vm
    cv
    #
    cA
    cB
    cmin
    co
    #
    caddc
    co
    #
    @0
    cdiv
    co
    #
    cmpt
    #
    c1
    cli
    wbr
    #
    wph
    vm
    cn
    @3
    cmpt
    #
    c1
    cc0
    caddc
    co
    #
    cli
    wbr
    #
    @5
    wph
    @6
    vm
    cn
    c1
    @1
    @0
    cdiv
    co
    #
    caddc
    co
    #
    cmpt
    #
    @7
    cli
    wph
    vm
    cn
    @3
    @10
    wph
    @0
    cn
    wcel
    #
    wa
    #
    @3
    @0
    @0
    cdiv
    co
    #
    @9
    caddc
    co
    @10
    @13
    @0
    @1
    @0
    @12
    @0
    cc
    wcel
    wph
    @0
    nncn
    adantl
    #
    wph
    @1
    cc
    wcel
    #
    @12
    wph
    cA
    cB
    divcnvlin.3
    wph
    cB
    divcnvlin.4
    zcnd
    subcld
    #
    adantr
    #
    @15
    @12
    @0
    cc0
    wne
    wph
    @0
    nnne0
    adantl
    #
    divdird
    @13
    @14
    c1
    @9
    caddc
    @13
    @0
    @15
    @19
    dividd
    oveq1d
    eqtrd
    mpteq2dva
    wph
    cc0
    c1
    vk
    vm
    cn
    @9
    cmpt
    #
    @11
    c1
    cvv
    cn
    nnuz
    wph
    1zzd
    wph
    @16
    @20
    cc0
    cli
    wbr
    @17
    @1
    vm
    divcnv
    syl
    wph
    1cnd
    @11
    cvv
    wcel
    wph
    vm
    cn
    @10
    nnex
    mptex
    a1i
    wph
    cn
    cc
    vk
    cv
    #
    @20
    wph
    vm
    cn
    @9
    cc
    @20
    @13
    @1
    @0
    @18
    @15
    @19
    divcld
    @20
    eqid
    #
    fmptd
    ffvelrnda
    @21
    cn
    wcel
    #
    @21
    @11
    cfv
    #
    c1
    @21
    @20
    cfv
    #
    caddc
    co
    #
    wceq
    wph
    @23
    @24
    c1
    @1
    @21
    cdiv
    co
    #
    caddc
    co
    #
    @26
    vm
    @21
    @10
    @28
    cn
    @11
    vm
    vk
    weq
    @9
    @27
    c1
    caddc
    @0
    @21
    @1
    cdiv
    oveq2
    #
    oveq2d
    @11
    eqid
    c1
    @27
    caddc
    ovex
    fvmpt
    @23
    @25
    @27
    c1
    caddc
    vm
    @21
    @9
    @27
    cn
    @20
    @29
    @22
    @1
    @21
    cdiv
    ovex
    fvmpt
    oveq2d
    eqtr4d
    adantl
    climaddc2
    eqbrtrd
    @8
    @4
    c1
    cuz
    cfv
    #
    cres
    #
    c1
    cli
    wbr
    #
    @5
    @6
    @31
    @7
    c1
    cli
    @4
    cn
    cres
    #
    @6
    @31
    cn
    cz
    wss
    @33
    @6
    wceq
    nnssz
    vm
    cz
    cn
    @3
    resmpt
    ax-mp
    cn
    @30
    @4
    nnuz
    reseq2i
    eqtr3i
    1p0e1
    breq12i
    c1
    cz
    wcel
    @4
    cvv
    wcel
    #
    @32
    @5
    wb
    1z
    vm
    cz
    @3
    zex
    mptex
    #
    c1
    @4
    c1
    cvv
    climres
    mp2an
    bitri
    sylib
    wph
    c1
    vk
    cF
    @4
    cB
    cM
    cV
    cvv
    cZ
    divcnvlin.1
    divcnvlin.2
    divcnvlin.4
    divcnvlin.5
    @34
    wph
    @35
    a1i
    wph
    @21
    cZ
    wcel
    #
    wa
    #
    @21
    cB
    caddc
    co
    #
    @1
    caddc
    co
    #
    @38
    cdiv
    co
    #
    @21
    cA
    caddc
    co
    #
    @38
    cdiv
    co
    @38
    @4
    cfv
    #
    @21
    cF
    cfv
    @37
    @39
    @41
    @38
    cdiv
    @37
    @21
    cB
    cA
    @36
    @21
    cc
    wcel
    wph
    @36
    @21
    @21
    cz
    wcel
    #
    @21
    cM
    cuz
    cfv
    cZ
    cM
    @21
    eluzelz
    divcnvlin.1
    eleq2s
    #
    zcnd
    adantl
    @37
    cB
    wph
    cB
    cz
    wcel
    @36
    divcnvlin.4
    adantr
    #
    zcnd
    wph
    cA
    cc
    wcel
    @36
    divcnvlin.3
    adantr
    ppncand
    oveq1d
    @37
    @38
    cz
    wcel
    @42
    @40
    wceq
    @37
    @21
    cB
    @36
    @43
    wph
    @44
    adantl
    @45
    zaddcld
    vm
    @38
    @3
    @40
    cz
    @4
    @0
    @38
    wceq
    #
    @2
    @39
    @0
    @38
    cdiv
    @0
    @38
    @1
    caddc
    oveq1
    @46
    id
    oveq12d
    @4
    eqid
    @39
    @38
    cdiv
    ovex
    fvmpt
    syl
    divcnvlin.6
    3eqtr4d
    climshft2
    mpbird
end
