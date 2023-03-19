include "csn.mm"
include "cun.mm"
include "cint.mm"
include "cin.mm"
include "intun.mm"
include "intsn.mm"
include "ineq2i.mm"
include "eqtri.mm"

theorem intunsn
  let cA: class A
  let cB: class B
  assume intunsn.1: |- B e. _V


  assert |- |^| ( A u. { B } ) = ( |^| A i^i B )

  proof
    cA
    cB
    csn
    #
    cun
    cint
    cA
    cint
    #
    @0
    cint
    #
    cin
    @1
    cB
    cin
    cA
    @0
    intun
    @2
    cB
    @1
    cB
    intunsn.1
    intsn
    ineq2i
    eqtri
end
