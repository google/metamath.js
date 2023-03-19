include "csu.mm"
include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "cfv.mm"
include "c0.mm"
include "isum.mm"
include "cdm.mm"
include "wcel.mm"
include "wn.mm"
include "wceq.mm"
include "ndmfv.mm"
include "syl.mm"
include "eqtrd.mm"

theorem sumnul
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vm: setvar m
  let cB: class B
  assume isumcl.1: |- Z = ( ZZ>= ` M )
  assume isumcl.2: |- ( ph -> M e. ZZ )
  assume isumcl.3: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = A )
  assume isumcl.4: |- ( ( ph /\ k e. Z ) -> A e. CC )
  assume sumnul.5: |- ( ph -> -. seq M ( + , F ) e. dom ~~> )

  disjoint F k
  disjoint k ph
  disjoint Z k
  disjoint M k
  disjoint A m
  disjoint k m
  disjoint B k
  disjoint B m
  disjoint F m
  disjoint m ph
  disjoint Z m
  disjoint M m
  assert |- ( ph -> sum_ k e. Z A = (/) )

  proof
    wph
    cZ
    cA
    vk
    csu
    caddc
    cF
    cM
    cseq
    #
    cli
    cfv
    #
    c0
    wph
    cA
    vk
    cF
    cM
    cZ
    isumcl.1
    isumcl.2
    isumcl.3
    isumcl.4
    isum
    wph
    @0
    cli
    cdm
    wcel
    wn
    @1
    c0
    wceq
    sumnul.5
    @0
    cli
    ndmfv
    syl
    eqtrd
end
