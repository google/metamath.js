include "cv.mm"
include "cec.mm"
include "wceq.mm"
include "wrex.mm"
include "cqs.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "df-qs.mm"
include "elab2g.mm"

theorem elqsg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint R x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint R y
  assert |- ( B e. V -> ( B e. ( A /. R ) <-> E. x e. A B = [ x ] R ) )

  proof
    vy
    cv
    #
    vx
    cv
    cR
    cec
    #
    wceq
    #
    vx
    cA
    wrex
    cB
    @1
    wceq
    #
    vx
    cA
    wrex
    vy
    cB
    cA
    cR
    cqs
    cV
    @0
    cB
    wceq
    @2
    @3
    vx
    cA
    @0
    cB
    @1
    eqeq1
    rexbidv
    vx
    vy
    cA
    cR
    df-qs
    elab2g
end
