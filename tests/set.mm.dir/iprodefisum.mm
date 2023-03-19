include "ce.mm"
include "cfv.mm"
include "cv.mm"
include "cmpt.mm"
include "ccom.mm"
include "csu.mm"
include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "isumcl.mm"
include "efne0.mm"
include "syl.mm"
include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "cmul.mm"
include "ccncf.mm"
include "co.mm"
include "efcn.mm"
include "a1i.mm"
include "wa.mm"
include "wceq.mm"
include "fveq2.mm"
include "eqid.mm"
include "fvex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "eqeltrd.mm"
include "serf.mm"
include "cuz.mm"
include "eqcomi.mm"
include "eleq2s.mm"
include "seqfeq.mm"
include "cdm.mm"
include "wbr.mm"
include "climdm.mm"
include "sylib.mm"
include "eqbrtrd.mm"
include "climcl.mm"
include "climcncf.mm"
include "cbvmptv.mm"
include "fmptd.mm"
include "iprodefisumlem.mm"
include "isum.mm"
include "fveq2d.mm"
include "3brtr4d.mm"
include "wf.mm"
include "fvco3.mm"
include "sylan.mm"
include "3eqtrd.mm"
include "efcl.mm"
include "iprodn0.mm"

theorem iprodefisum
  let wph: wff ph
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  assume iprodefisum.1: |- Z = ( ZZ>= ` M )
  assume iprodefisum.2: |- ( ph -> M e. ZZ )
  assume iprodefisum.3: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = B )
  assume iprodefisum.4: |- ( ( ph /\ k e. Z ) -> B e. CC )
  assume iprodefisum.5: |- ( ph -> seq M ( + , F ) e. dom ~~> )

  disjoint F k
  disjoint k ph
  disjoint M k
  disjoint Z k
  disjoint F j
  disjoint j k
  disjoint Z j
  disjoint j ph
  disjoint M j
  assert |- ( ph -> prod_ k e. Z ( exp ` B ) = ( exp ` sum_ k e. Z B ) )

  proof
    wph
    cB
    ce
    cfv
    #
    vk
    ce
    vj
    cZ
    vj
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    ccom
    #
    cM
    cZ
    cB
    vk
    csu
    #
    ce
    cfv
    #
    cZ
    iprodefisum.1
    iprodefisum.2
    wph
    @5
    cc
    wcel
    @6
    cc0
    wne
    wph
    cB
    vk
    cF
    cM
    cZ
    iprodefisum.1
    iprodefisum.2
    iprodefisum.3
    iprodefisum.4
    iprodefisum.5
    isumcl
    @5
    efne0
    syl
    wph
    ce
    caddc
    @3
    cM
    cseq
    #
    ccom
    caddc
    cF
    cM
    cseq
    #
    cli
    cfv
    #
    ce
    cfv
    cmul
    @4
    cM
    cseq
    @6
    cli
    wph
    cc
    cc
    @9
    ce
    @7
    cM
    cZ
    iprodefisum.1
    iprodefisum.2
    ce
    cc
    cc
    ccncf
    co
    wcel
    wph
    efcn
    a1i
    wph
    vk
    @3
    cM
    cZ
    iprodefisum.1
    iprodefisum.2
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @10
    @3
    cfv
    #
    @10
    cF
    cfv
    #
    cc
    @11
    @13
    @14
    wceq
    #
    wph
    vj
    @10
    @2
    @14
    cZ
    @3
    @1
    @10
    cF
    fveq2
    #
    @3
    eqid
    @10
    cF
    fvex
    fvmpt
    #
    adantl
    #
    @12
    @14
    cB
    cc
    iprodefisum.3
    iprodefisum.4
    eqeltrd
    #
    eqeltrd
    serf
    wph
    @7
    @8
    @9
    cli
    wph
    caddc
    vk
    @3
    cF
    cM
    iprodefisum.2
    @10
    cM
    cuz
    cfv
    #
    wcel
    @15
    wph
    @15
    @10
    cZ
    @20
    @17
    cZ
    @20
    iprodefisum.1
    eqcomi
    eleq2s
    adantl
    seqfeq
    wph
    @8
    cli
    cdm
    wcel
    @8
    @9
    cli
    wbr
    #
    iprodefisum.5
    @8
    climdm
    sylib
    #
    eqbrtrd
    wph
    @21
    @9
    cc
    wcel
    @22
    @9
    @8
    climcl
    syl
    climcncf
    wph
    @3
    cM
    cZ
    iprodefisum.1
    iprodefisum.2
    wph
    vk
    cZ
    @14
    cc
    @3
    @19
    vj
    vk
    cZ
    @2
    @14
    @16
    cbvmptv
    fmptd
    #
    iprodefisumlem
    wph
    @5
    @9
    ce
    wph
    cB
    vk
    cF
    cM
    cZ
    iprodefisum.1
    iprodefisum.2
    iprodefisum.3
    iprodefisum.4
    isum
    fveq2d
    3brtr4d
    @12
    @10
    @4
    cfv
    #
    @13
    ce
    cfv
    #
    @14
    ce
    cfv
    @0
    wph
    cZ
    cc
    @3
    wf
    @11
    @24
    @25
    wceq
    @23
    cZ
    cc
    @10
    ce
    @3
    fvco3
    sylan
    @12
    @13
    @14
    ce
    @18
    fveq2d
    @12
    @14
    cB
    ce
    iprodefisum.3
    fveq2d
    3eqtrd
    @12
    cB
    cc
    wcel
    @0
    cc
    wcel
    iprodefisum.4
    cB
    efcl
    syl
    iprodn0
end
