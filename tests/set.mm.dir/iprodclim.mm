include "cprod.mm"
include "cmul.mm"
include "cseq.mm"
include "cli.mm"
include "cfv.mm"
include "iprod.mm"
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

theorem iprodclim
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cZ: class Z
  assume iprodclim.1: |- Z = ( ZZ>= ` M )
  assume iprodclim.2: |- ( ph -> M e. ZZ )
  assume iprodclim.3: |- ( ph -> E. n e. Z E. y ( y =/= 0 /\ seq n ( x. , F ) ~~> y ) )
  assume iprodclim.4: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = A )
  assume iprodclim.5: |- ( ( ph /\ k e. Z ) -> A e. CC )
  assume iprodclim.6: |- ( ph -> seq M ( x. , F ) ~~> B )

  disjoint A n
  disjoint A y
  disjoint F k
  disjoint k n
  disjoint k ph
  disjoint k y
  disjoint M k
  disjoint M y
  disjoint n ph
  disjoint n y
  disjoint ph y
  disjoint Z k
  disjoint Z n
  disjoint Z y
  assert |- ( ph -> prod_ k e. Z A = B )

  proof
    wph
    cZ
    cA
    vk
    cprod
    cmul
    cF
    cM
    cseq
    #
    cli
    cfv
    #
    cB
    wph
    vy
    cA
    vk
    vn
    cF
    cM
    cZ
    iprodclim.1
    iprodclim.2
    iprodclim.3
    iprodclim.4
    iprodclim.5
    iprod
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
    iprodclim.6
    @0
    cB
    cli
    funbrfv
    mpsyl
    eqtrd
end
