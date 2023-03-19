include "csu.mm"
include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "cfv.mm"
include "isum.mm"
include "wfun.mm"
include "wbr.mm"
include "wceq.mm"
include "cdm.mm"
include "cc.mm"
include "wf.mm"
include "fclim.mm"
include "ffun.mm"
include "ax-mp.mm"
include "funbrfv.mm"
include "mpsyl.mm"
include "eqtrd.mm"

theorem isumclim
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  assume isumclim.1: |- Z = ( ZZ>= ` M )
  assume isumclim.2: |- ( ph -> M e. ZZ )
  assume isumclim.3: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = A )
  assume isumclim.4: |- ( ( ph /\ k e. Z ) -> A e. CC )
  assume isumclim.6: |- ( ph -> seq M ( + , F ) ~~> B )

  disjoint F k
  disjoint M k
  disjoint k ph
  disjoint Z k
  assert |- ( ph -> sum_ k e. Z A = B )

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
    cB
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
    cli
    wfun
    #
    wph
    @0
    cB
    cli
    wbr
    @1
    cB
    wceq
    cli
    cdm
    #
    cc
    cli
    wf
    @2
    fclim
    @3
    cc
    cli
    ffun
    ax-mp
    isumclim.6
    @0
    cB
    cli
    funbrfv
    mpsyl
    eqtrd
end
