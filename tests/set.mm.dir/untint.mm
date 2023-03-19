include "wel.mm"
include "wn.mm"
include "cv.mm"
include "wral.mm"
include "cint.mm"
include "wcel.mm"
include "wss.mm"
include "wi.mm"
include "intss1.mm"
include "ssralv.mm"
include "syl.mm"
include "rexlimiv.mm"

theorem untint
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( E. x e. A A. y e. x -. y e. y -> A. y e. |^| A -. y e. y )

  proof
    vy
    vy
    wel
    wn
    #
    vy
    vx
    cv
    #
    wral
    #
    @0
    vy
    cA
    cint
    #
    wral
    #
    vx
    cA
    @1
    cA
    wcel
    @3
    @1
    wss
    @2
    @4
    wi
    @1
    cA
    intss1
    @0
    vy
    @3
    @1
    ssralv
    syl
    rexlimiv
end
