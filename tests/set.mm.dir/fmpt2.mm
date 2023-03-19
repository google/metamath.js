include "wcel.mm"
include "wral.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "wf.mm"
include "fmpt2x.mm"
include "iunxpconst.mm"
include "feq2i.mm"
include "bitri.mm"

theorem fmpt2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  assume fmpt2.1: |- F = ( x e. A , y e. B |-> C )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint D x
  disjoint D y
  assert |- ( A. x e. A A. y e. B C e. D <-> F : ( A X. B ) --> D )

  proof
    cC
    cD
    wcel
    vy
    cB
    wral
    vx
    cA
    wral
    vx
    cA
    vx
    cv
    csn
    cB
    cxp
    ciun
    #
    cD
    cF
    wf
    cA
    cB
    cxp
    #
    cD
    cF
    wf
    vx
    vy
    cA
    cB
    cC
    cD
    cF
    fmpt2.1
    fmpt2x
    @0
    @1
    cD
    cF
    vx
    cA
    cB
    iunxpconst
    feq2i
    bitri
end
