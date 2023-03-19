include "cop.mm"
include "wceq.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "opeqex.mm"
include "opex.mm"
include "biantrur.mm"
include "3bitr4g.mm"

theorem oteqex2
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cT: class T


  assert |- ( <. <. A , B >. , C >. = <. <. R , S >. , T >. -> ( C e. _V <-> T e. _V ) )

  proof
    cA
    cB
    cop
    #
    cC
    cop
    cR
    cS
    cop
    #
    cT
    cop
    wceq
    @0
    cvv
    wcel
    #
    cC
    cvv
    wcel
    #
    wa
    @1
    cvv
    wcel
    #
    cT
    cvv
    wcel
    #
    wa
    @3
    @5
    @0
    cC
    @1
    cT
    opeqex
    @2
    @3
    cA
    cB
    opex
    biantrur
    @4
    @5
    cR
    cS
    opex
    biantrur
    3bitr4g
end
