include "cch.mm"
include "wcel.mm"
include "cort.mm"
include "cfv.mm"
include "cin.mm"
include "c0h.mm"
include "wceq.mm"
include "cif.mm"
include "id.mm"
include "fveq2.mm"
include "ineq12d.mm"
include "eqeq1d.mm"
include "h0elch.mm"
include "elimel.mm"
include "chocini.mm"
include "dedth.mm"

theorem chocin
  let cA: class A


  assert |- ( A e. CH -> ( A i^i ( _|_ ` A ) ) = 0H )

  proof
    cA
    cch
    wcel
    #
    cA
    cA
    cort
    cfv
    #
    cin
    #
    c0h
    wceq
    @0
    cA
    c0h
    cif
    #
    @3
    cort
    cfv
    #
    cin
    #
    c0h
    wceq
    cA
    c0h
    cA
    @3
    wceq
    #
    @2
    @5
    c0h
    @6
    cA
    @3
    @1
    @4
    @6
    id
    cA
    @3
    cort
    fveq2
    ineq12d
    eqeq1d
    @3
    cA
    c0h
    cch
    h0elch
    elimel
    chocini
    dedth
end
