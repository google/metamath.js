include "cli.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "crli.mm"
include "cz.mm"
include "wcel.mm"
include "wb.mm"
include "eqid.mm"
include "climmpt.mm"
include "syl2anc.mm"
include "cc.mm"
include "wral.mm"
include "ralrimiva.mm"
include "weq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "cbvralv.mm"
include "bitri.mm"
include "sylib.mm"
include "r19.21bi.mm"
include "fmptd.mm"
include "rlimclim.mm"
include "bitr4d.mm"

theorem climmpt2
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vm: setvar m
  assume climmpt2.1: |- Z = ( ZZ>= ` M )
  assume climmpt2.2: |- ( ph -> M e. ZZ )
  assume climmpt2.3: |- ( ph -> F e. V )
  assume climmpt2.5: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC )

  disjoint F k
  disjoint Z k
  disjoint k ph
  disjoint F n
  disjoint A n
  disjoint Z n
  disjoint n ph
  disjoint k m
  disjoint F m
  disjoint Z m
  disjoint m n
  assert |- ( ph -> ( F ~~> A <-> ( n e. Z |-> ( F ` n ) ) ~~>r A ) )

  proof
    wph
    cF
    cA
    cli
    wbr
    #
    vn
    cZ
    vn
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    cA
    cli
    wbr
    #
    @3
    cA
    crli
    wbr
    wph
    cM
    cz
    wcel
    cF
    cV
    wcel
    @0
    @4
    wb
    climmpt2.2
    climmpt2.3
    cA
    vn
    cF
    @3
    cM
    cV
    cZ
    climmpt2.1
    @3
    eqid
    #
    climmpt
    syl2anc
    wph
    cA
    @3
    cM
    cZ
    climmpt2.1
    climmpt2.2
    wph
    vn
    cZ
    @2
    cc
    @3
    wph
    @2
    cc
    wcel
    #
    vn
    cZ
    wph
    vk
    cv
    #
    cF
    cfv
    #
    cc
    wcel
    #
    vk
    cZ
    wral
    #
    @6
    vn
    cZ
    wral
    #
    wph
    @9
    vk
    cZ
    climmpt2.5
    ralrimiva
    @10
    vm
    cv
    #
    cF
    cfv
    #
    cc
    wcel
    #
    vm
    cZ
    wral
    @11
    @9
    @14
    vk
    vm
    cZ
    vk
    vm
    weq
    @8
    @13
    cc
    @7
    @12
    cF
    fveq2
    eleq1d
    cbvralv
    @14
    @6
    vm
    vn
    cZ
    vm
    vn
    weq
    @13
    @2
    cc
    @12
    @1
    cF
    fveq2
    eleq1d
    cbvralv
    bitri
    sylib
    r19.21bi
    @5
    fmptd
    rlimclim
    bitr4d
end
