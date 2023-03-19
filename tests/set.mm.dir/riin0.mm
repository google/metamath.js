include "c0.mm"
include "wceq.mm"
include "ciin.mm"
include "cin.mm"
include "iineq1.mm"
include "ineq2d.mm"
include "cvv.mm"
include "0iin.mm"
include "ineq2i.mm"
include "inv1.mm"
include "eqtri.mm"
include "syl6eq.mm"

theorem riin0
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cX: class X
  let vy: setvar y
  let cB: class B

  disjoint A x
  disjoint X x
  disjoint A y
  disjoint x y
  disjoint X y
  disjoint B x
  assert |- ( X = (/) -> ( A i^i |^|_ x e. X S ) = A )

  proof
    cX
    c0
    wceq
    #
    cA
    vx
    cX
    cS
    ciin
    #
    cin
    cA
    vx
    c0
    cS
    ciin
    #
    cin
    #
    cA
    @0
    @1
    @2
    cA
    vx
    cX
    c0
    cS
    iineq1
    ineq2d
    @3
    cA
    cvv
    cin
    cA
    @2
    cvv
    cA
    vx
    cS
    0iin
    ineq2i
    cA
    inv1
    eqtri
    syl6eq
end
