include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "cfv.mm"
include "wn.mm"
include "wral.mm"
include "ismri2d.mm"
include "mpbird.mm"

theorem ismri2dd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cI: class I
  let cN: class N
  let cX: class X
  assume ismri2.1: |- N = ( mrCls ` A )
  assume ismri2.2: |- I = ( mrInd ` A )
  assume ismri2d.3: |- ( ph -> A e. ( Moore ` X ) )
  assume ismri2d.4: |- ( ph -> S C_ X )
  assume ismri2dd.5: |- ( ph -> A. x e. S -. x e. ( N ` ( S \ { x } ) ) )

  disjoint A x
  disjoint S x
  assert |- ( ph -> S e. I )

  proof
    wph
    cS
    cI
    wcel
    vx
    cv
    #
    cS
    @0
    csn
    cdif
    cN
    cfv
    wcel
    wn
    vx
    cS
    wral
    ismri2dd.5
    wph
    vx
    cA
    cS
    cI
    cN
    cX
    ismri2.1
    ismri2.2
    ismri2d.3
    ismri2d.4
    ismri2d
    mpbird
end
