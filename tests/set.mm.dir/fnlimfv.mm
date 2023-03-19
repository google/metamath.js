include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cli.mm"
include "cvv.mm"
include "wceq.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfmpt.mm"
include "fveq2.mm"
include "mpteq2dv.mm"
include "fveq2d.mm"
include "cbvmptf.mm"
include "eqtri.mm"
include "a1i.mm"
include "adantl.mm"
include "fvexd.mm"
include "fvmptd.mm"

theorem fnlimfv
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let vm: setvar m
  let cF: class F
  let cG: class G
  let cX: class X
  let cZ: class Z
  let vy: setvar y
  assume fnlimfv.1: |- F/_ x D
  assume fnlimfv.2: |- F/_ x F
  assume fnlimfv.3: |- G = ( x e. D |-> ( ~~> ` ( m e. Z |-> ( ( F ` m ) ` x ) ) ) )
  assume fnlimfv.4: |- ( ph -> X e. D )

  disjoint X m
  disjoint Z x
  disjoint m x
  disjoint D y
  disjoint F y
  disjoint X y
  disjoint m y
  disjoint Z y
  disjoint x y
  disjoint ph y
  assert |- ( ph -> ( G ` X ) = ( ~~> ` ( m e. Z |-> ( ( F ` m ) ` X ) ) ) )

  proof
    wph
    vy
    cX
    vm
    cZ
    vy
    cv
    #
    vm
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cmpt
    #
    cli
    cfv
    #
    vm
    cZ
    cX
    @2
    cfv
    #
    cmpt
    #
    cli
    cfv
    #
    cD
    cG
    cvv
    cG
    vy
    cD
    @5
    cmpt
    #
    wceq
    wph
    cG
    vx
    cD
    vm
    cZ
    vx
    cv
    #
    @2
    cfv
    #
    cmpt
    #
    cli
    cfv
    #
    cmpt
    @9
    fnlimfv.3
    vx
    vy
    cD
    @13
    @5
    fnlimfv.1
    vy
    cD
    nfcv
    vy
    @13
    nfcv
    vx
    @4
    cli
    vx
    cli
    nfcv
    vx
    vm
    cZ
    @3
    vx
    cZ
    nfcv
    vx
    @0
    @2
    vx
    @1
    cF
    fnlimfv.2
    vx
    @1
    nfcv
    nffv
    vx
    @0
    nfcv
    nffv
    nfmpt
    nffv
    @10
    @0
    wceq
    #
    @12
    @4
    cli
    @14
    vm
    cZ
    @11
    @3
    @10
    @0
    @2
    fveq2
    mpteq2dv
    fveq2d
    cbvmptf
    eqtri
    a1i
    @0
    cX
    wceq
    #
    @5
    @8
    wceq
    wph
    @15
    @4
    @7
    cli
    @15
    vm
    cZ
    @3
    @6
    @0
    cX
    @2
    fveq2
    mpteq2dv
    fveq2d
    adantl
    fnlimfv.4
    wph
    @7
    cli
    fvexd
    fvmptd
end
