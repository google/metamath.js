include "cch.mm"
include "wcel.mm"
include "c0h.mm"
include "cin.mm"
include "wceq.mm"
include "cif.mm"
include "ineq1.mm"
include "eqeq1d.mm"
include "h0elch.mm"
include "elimel.mm"
include "chm0i.mm"
include "dedth.mm"

theorem chm0
  let cA: class A


  assert |- ( A e. CH -> ( A i^i 0H ) = 0H )

  proof
    cA
    cch
    wcel
    #
    cA
    c0h
    cin
    #
    c0h
    wceq
    @0
    cA
    c0h
    cif
    #
    c0h
    cin
    #
    c0h
    wceq
    cA
    c0h
    cA
    @2
    wceq
    @1
    @3
    c0h
    cA
    @2
    c0h
    ineq1
    eqeq1d
    @2
    cA
    c0h
    cch
    h0elch
    elimel
    chm0i
    dedth
end
