include "cprod.mm"
include "cmul.mm"
include "cseq.mm"
include "cli.mm"
include "cfv.mm"
include "ntrivcvgn0.mm"
include "zprod.mm"
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

theorem zprodn0
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vm: setvar m
  let vx: setvar x
  assume zprodn0.1: |- Z = ( ZZ>= ` M )
  assume zprodn0.2: |- ( ph -> M e. ZZ )
  assume zprodn0.3: |- ( ph -> X =/= 0 )
  assume zprodn0.4: |- ( ph -> seq M ( x. , F ) ~~> X )
  assume zprodn0.5: |- ( ph -> A C_ Z )
  assume zprodn0.6: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = if ( k e. A , B , 1 ) )
  assume zprodn0.7: |- ( ( ph /\ k e. A ) -> B e. CC )

  disjoint A k
  disjoint F k
  disjoint k ph
  disjoint M k
  disjoint A m
  disjoint A x
  disjoint B m
  disjoint B x
  disjoint F m
  disjoint F x
  disjoint k m
  disjoint k x
  disjoint M m
  disjoint m ph
  disjoint m x
  disjoint M x
  disjoint ph x
  disjoint X x
  disjoint Z m
  disjoint Z x
  assert |- ( ph -> prod_ k e. A B = X )

  proof
    wph
    cA
    cB
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
    cX
    wph
    vx
    cA
    cB
    vk
    vm
    cF
    cM
    cZ
    zprodn0.1
    zprodn0.2
    wph
    vx
    vm
    cF
    cM
    cX
    cZ
    zprodn0.1
    zprodn0.2
    zprodn0.4
    zprodn0.3
    ntrivcvgn0
    zprodn0.5
    zprodn0.6
    zprodn0.7
    zprod
    cli
    wfun
    #
    wph
    @0
    cX
    cli
    wbr
    @1
    cX
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
    zprodn0.4
    @0
    cX
    cli
    funbrfv
    mpsyl
    eqtrd
end
