include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "wn.mm"
include "wral.mm"
include "ismri.mm"
include "baibd.mm"

theorem ismri2
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cI: class I
  let cN: class N
  let cX: class X
  assume ismri2.1: |- N = ( mrCls ` A )
  assume ismri2.2: |- I = ( mrInd ` A )

  disjoint A x
  disjoint S x
  assert |- ( ( A e. ( Moore ` X ) /\ S C_ X ) -> ( S e. I <-> A. x e. S -. x e. ( N ` ( S \ { x } ) ) ) )

  proof
    cA
    cX
    cmre
    cfv
    wcel
    cS
    cI
    wcel
    cS
    cX
    wss
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
    vx
    cA
    cS
    cI
    cN
    cX
    ismri2.1
    ismri2.2
    ismri
    baibd
end
