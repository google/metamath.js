include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "cfv.mm"
include "csu.mm"
include "cdm.mm"
include "wcel.mm"
include "wbr.mm"
include "climdm.mm"
include "sylib.mm"
include "isum.mm"
include "breqtrrd.mm"

theorem isumclim2
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  assume isumclim.1: |- Z = ( ZZ>= ` M )
  assume isumclim.2: |- ( ph -> M e. ZZ )
  assume isumclim.3: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = A )
  assume isumclim.4: |- ( ( ph /\ k e. Z ) -> A e. CC )
  assume isumclim2.5: |- ( ph -> seq M ( + , F ) e. dom ~~> )

  disjoint F k
  disjoint M k
  disjoint k ph
  disjoint Z k
  assert |- ( ph -> seq M ( + , F ) ~~> sum_ k e. Z A )

  proof
    wph
    caddc
    cF
    cM
    cseq
    #
    @0
    cli
    cfv
    #
    cZ
    cA
    vk
    csu
    cli
    wph
    @0
    cli
    cdm
    wcel
    @0
    @1
    cli
    wbr
    isumclim2.5
    @0
    climdm
    sylib
    wph
    cA
    vk
    cF
    cM
    cZ
    isumclim.1
    isumclim.2
    isumclim.3
    isumclim.4
    isum
    breqtrrd
end
