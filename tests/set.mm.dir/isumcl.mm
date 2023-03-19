include "csu.mm"
include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "cfv.mm"
include "cc.mm"
include "isum.mm"
include "cdm.mm"
include "wf.mm"
include "wcel.mm"
include "fclim.mm"
include "ffvelrn.mm"
include "sylancr.mm"
include "eqeltrd.mm"

theorem isumcl
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
  assume isumcl.5: |- ( ph -> seq M ( + , F ) e. dom ~~> )

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
  assert |- ( ph -> sum_ k e. Z A e. CC )

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
    cc
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
    cli
    cdm
    #
    cc
    cli
    wf
    @0
    @2
    wcel
    @1
    cc
    wcel
    fclim
    isumcl.5
    @2
    cc
    @0
    cli
    ffvelrn
    sylancr
    eqeltrd
end
