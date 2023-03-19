include "cli.mm"
include "cfv.mm"
include "csu.mm"
include "cdm.mm"
include "wcel.mm"
include "wbr.mm"
include "climdm.mm"
include "sylib.mm"
include "caddc.mm"
include "cmpt.mm"
include "cseq.mm"
include "cv.mm"
include "sumfc.mm"
include "wa.mm"
include "eqidd.mm"
include "cc.mm"
include "eqid.mm"
include "fmptd.mm"
include "ffvelrnda.mm"
include "isum.mm"
include "syl5eqr.mm"
include "cio.mm"
include "cvv.mm"
include "seqex.mm"
include "a1i.mm"
include "cfz.mm"
include "co.mm"
include "cres.mm"
include "wss.mm"
include "wceq.mm"
include "cuz.mm"
include "fzssuz.mm"
include "sseqtr4i.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "fveq1i.mm"
include "fvres.mm"
include "syl5reqr.mm"
include "sumeq2i.mm"
include "eqtri.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "simpl.mm"
include "elfzuz.mm"
include "syl6eleqr.mm"
include "syl2an.mm"
include "fsumser.mm"
include "eqtr2d.mm"
include "climeq.mm"
include "iotabidv.mm"
include "df-fv.mm"
include "3eqtr4g.mm"
include "eqtrd.mm"
include "breqtrrd.mm"

theorem isumclim3
  let wph: wff ph
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vm: setvar m
  let vx: setvar x
  assume isumclim3.1: |- Z = ( ZZ>= ` M )
  assume isumclim3.2: |- ( ph -> M e. ZZ )
  assume isumclim3.3: |- ( ph -> F e. dom ~~> )
  assume isumclim3.4: |- ( ( ph /\ k e. Z ) -> A e. CC )
  assume isumclim3.5: |- ( ( ph /\ j e. Z ) -> ( F ` j ) = sum_ k e. ( M ... j ) A )

  disjoint A j
  disjoint j k
  disjoint M j
  disjoint M k
  disjoint j ph
  disjoint k ph
  disjoint Z j
  disjoint Z k
  disjoint F j
  disjoint j m
  disjoint j x
  disjoint m x
  disjoint A m
  disjoint A x
  disjoint k m
  disjoint k x
  disjoint M m
  disjoint M x
  disjoint m ph
  disjoint ph x
  disjoint Z m
  disjoint Z x
  disjoint F x
  assert |- ( ph -> F ~~> sum_ k e. Z A )

  proof
    wph
    cF
    cF
    cli
    cfv
    #
    cZ
    cA
    vk
    csu
    #
    cli
    wph
    cF
    cli
    cdm
    #
    wcel
    cF
    @0
    cli
    wbr
    isumclim3.3
    cF
    climdm
    sylib
    wph
    @1
    caddc
    vk
    cZ
    cA
    cmpt
    #
    cM
    cseq
    #
    cli
    cfv
    #
    @0
    wph
    @1
    cZ
    vm
    cv
    #
    @3
    cfv
    #
    vm
    csu
    @5
    cZ
    cA
    vm
    vk
    sumfc
    wph
    @7
    vm
    @3
    cM
    cZ
    isumclim3.1
    isumclim3.2
    wph
    @6
    cZ
    wcel
    #
    wa
    @7
    eqidd
    wph
    cZ
    cc
    @6
    @3
    wph
    vk
    cZ
    cA
    cc
    @3
    isumclim3.4
    @3
    eqid
    fmptd
    ffvelrnda
    #
    isum
    syl5eqr
    wph
    @4
    vx
    cv
    #
    cli
    wbr
    #
    vx
    cio
    cF
    @10
    cli
    wbr
    #
    vx
    cio
    @5
    @0
    wph
    @11
    @12
    vx
    wph
    @10
    vj
    @4
    cF
    cM
    cvv
    @2
    cZ
    isumclim3.1
    @4
    cvv
    wcel
    wph
    caddc
    @3
    cM
    seqex
    a1i
    isumclim3.3
    isumclim3.2
    wph
    vj
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @13
    cF
    cfv
    cM
    @13
    cfz
    co
    #
    cA
    vk
    csu
    #
    @13
    @4
    cfv
    #
    isumclim3.5
    @15
    @17
    @16
    @7
    vm
    csu
    #
    @18
    @19
    @16
    @6
    vk
    @16
    cA
    cmpt
    #
    cfv
    #
    vm
    csu
    @17
    @16
    @7
    @21
    vm
    @6
    @16
    wcel
    #
    @21
    @6
    @3
    @16
    cres
    #
    cfv
    @7
    @6
    @23
    @20
    @16
    cZ
    wss
    @23
    @20
    wceq
    @16
    cM
    cuz
    cfv
    #
    cZ
    cM
    @13
    fzssuz
    isumclim3.1
    sseqtr4i
    vk
    cZ
    @16
    cA
    resmpt
    ax-mp
    fveq1i
    @6
    @16
    @3
    fvres
    syl5reqr
    sumeq2i
    @16
    cA
    vm
    vk
    sumfc
    eqtri
    @15
    @7
    vm
    @3
    cM
    @13
    @15
    @22
    wa
    @7
    eqidd
    @15
    @13
    cZ
    @24
    wph
    @14
    simpr
    isumclim3.1
    syl6eleq
    @15
    wph
    @8
    @7
    cc
    wcel
    @22
    wph
    @14
    simpl
    @22
    @6
    @24
    cZ
    @6
    cM
    @13
    elfzuz
    isumclim3.1
    syl6eleqr
    @9
    syl2an
    fsumser
    syl5eqr
    eqtr2d
    climeq
    iotabidv
    vx
    @4
    cli
    df-fv
    vx
    cF
    cli
    df-fv
    3eqtr4g
    eqtrd
    breqtrrd
end
