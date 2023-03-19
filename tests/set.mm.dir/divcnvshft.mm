include "cc0.mm"
include "cli.mm"
include "wbr.mm"
include "cz.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "cmpt.mm"
include "cn.mm"
include "cc.mm"
include "wcel.mm"
include "divcnv.mm"
include "syl.mm"
include "c1.mm"
include "cuz.mm"
include "cfv.mm"
include "cres.mm"
include "wss.mm"
include "wceq.mm"
include "nnssz.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "nnuz.mm"
include "reseq2i.mm"
include "eqtr3i.mm"
include "breq1i.mm"
include "cvv.mm"
include "wb.mm"
include "1z.mm"
include "zex.mm"
include "mptex.mm"
include "climres.mm"
include "mp2an.mm"
include "bitri.mm"
include "sylib.mm"
include "a1i.mm"
include "wa.mm"
include "caddc.mm"
include "uzssz.mm"
include "eqsstri.mm"
include "sseli.mm"
include "adantl.mm"
include "adantr.mm"
include "zaddcld.mm"
include "oveq2.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "eqtr4d.mm"
include "climshft2.mm"
include "mpbird.mm"

theorem divcnvshft
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vm: setvar m
  assume divcnvshft.1: |- Z = ( ZZ>= ` M )
  assume divcnvshft.2: |- ( ph -> M e. ZZ )
  assume divcnvshft.3: |- ( ph -> A e. CC )
  assume divcnvshft.4: |- ( ph -> B e. ZZ )
  assume divcnvshft.5: |- ( ph -> F e. V )
  assume divcnvshft.6: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = ( A / ( k + B ) ) )

  disjoint A k
  disjoint B k
  disjoint F k
  disjoint k ph
  disjoint M k
  disjoint Z k
  disjoint A m
  disjoint B m
  disjoint k m
  assert |- ( ph -> F ~~> 0 )

  proof
    wph
    cF
    cc0
    cli
    wbr
    vm
    cz
    cA
    vm
    cv
    #
    cdiv
    co
    #
    cmpt
    #
    cc0
    cli
    wbr
    #
    wph
    vm
    cn
    @1
    cmpt
    #
    cc0
    cli
    wbr
    #
    @3
    wph
    cA
    cc
    wcel
    @5
    divcnvshft.3
    cA
    vm
    divcnv
    syl
    @5
    @2
    c1
    cuz
    cfv
    #
    cres
    #
    cc0
    cli
    wbr
    #
    @3
    @4
    @7
    cc0
    cli
    @2
    cn
    cres
    #
    @4
    @7
    cn
    cz
    wss
    @9
    @4
    wceq
    nnssz
    vm
    cz
    cn
    @1
    resmpt
    ax-mp
    cn
    @6
    @2
    nnuz
    reseq2i
    eqtr3i
    breq1i
    c1
    cz
    wcel
    @2
    cvv
    wcel
    #
    @8
    @3
    wb
    1z
    vm
    cz
    @1
    zex
    mptex
    #
    cc0
    @2
    c1
    cvv
    climres
    mp2an
    bitri
    sylib
    wph
    cc0
    vk
    cF
    @2
    cB
    cM
    cV
    cvv
    cZ
    divcnvshft.1
    divcnvshft.2
    divcnvshft.4
    divcnvshft.5
    @10
    wph
    @11
    a1i
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @12
    cB
    caddc
    co
    #
    @2
    cfv
    #
    cA
    @15
    cdiv
    co
    #
    @12
    cF
    cfv
    @14
    @15
    cz
    wcel
    @16
    @17
    wceq
    @14
    @12
    cB
    @13
    @12
    cz
    wcel
    wph
    cZ
    cz
    @12
    cZ
    cM
    cuz
    cfv
    cz
    divcnvshft.1
    cM
    uzssz
    eqsstri
    sseli
    adantl
    wph
    cB
    cz
    wcel
    @13
    divcnvshft.4
    adantr
    zaddcld
    vm
    @15
    @1
    @17
    cz
    @2
    @0
    @15
    cA
    cdiv
    oveq2
    @2
    eqid
    cA
    @15
    cdiv
    ovex
    fvmpt
    syl
    divcnvshft.6
    eqtr4d
    climshft2
    mpbird
end
