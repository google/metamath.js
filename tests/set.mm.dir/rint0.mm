include "c0.mm"
include "wceq.mm"
include "cint.mm"
include "cin.mm"
include "inteq.mm"
include "ineq2d.mm"
include "cvv.mm"
include "int0.mm"
include "ineq2i.mm"
include "inv1.mm"
include "eqtri.mm"
include "syl6eq.mm"

theorem rint0
  let cA: class A
  let cX: class X


  assert |- ( X = (/) -> ( A i^i |^| X ) = A )

  proof
    cX
    c0
    wceq
    #
    cA
    cX
    cint
    #
    cin
    cA
    c0
    cint
    #
    cin
    #
    cA
    @0
    @1
    @2
    cA
    cX
    c0
    inteq
    ineq2d
    @3
    cA
    cvv
    cin
    cA
    @2
    cvv
    cA
    int0
    ineq2i
    cA
    inv1
    eqtri
    syl6eq
end
