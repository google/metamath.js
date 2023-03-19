include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "wn.mm"
include "wral.mm"
include "wb.mm"
include "ismri2.mm"
include "syl2anc.mm"

theorem ismri2d
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

  disjoint A x
  disjoint S x
  assert |- ( ph -> ( S e. I <-> A. x e. S -. x e. ( N ` ( S \ { x } ) ) ) )

  proof
    wph
    cA
    cX
    cmre
    cfv
    wcel
    cS
    cX
    wss
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
    wb
    ismri2d.3
    ismri2d.4
    vx
    cA
    cS
    cI
    cN
    cX
    ismri2.1
    ismri2.2
    ismri2
    syl2anc
end
