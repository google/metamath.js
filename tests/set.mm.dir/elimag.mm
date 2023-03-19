include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "cima.mm"
include "wceq.mm"
include "breq2.mm"
include "rexbidv.mm"
include "dfima2.mm"
include "elab2g.mm"

theorem elimag
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C y
  assert |- ( A e. V -> ( A e. ( B " C ) <-> E. x e. C x B A ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cB
    wbr
    #
    vx
    cC
    wrex
    @0
    cA
    cB
    wbr
    #
    vx
    cC
    wrex
    vy
    cA
    cB
    cC
    cima
    cV
    @1
    cA
    wceq
    @2
    @3
    vx
    cC
    @1
    cA
    @0
    cB
    breq2
    rexbidv
    vx
    vy
    cB
    cC
    dfima2
    elab2g
end
