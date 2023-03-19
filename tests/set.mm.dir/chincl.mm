include "cch.mm"
include "wcel.mm"
include "cin.mm"
include "chil.mm"
include "cif.mm"
include "wceq.mm"
include "ineq1.mm"
include "eleq1d.mm"
include "ineq2.mm"
include "ifchhv.mm"
include "chincli.mm"
include "dedth2h.mm"

theorem chincl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( A i^i B ) e. CH )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    cA
    cB
    cin
    #
    cch
    wcel
    @0
    cA
    chil
    cif
    #
    cB
    cin
    #
    cch
    wcel
    @3
    @1
    cB
    chil
    cif
    #
    cin
    #
    cch
    wcel
    cA
    cB
    chil
    chil
    cA
    @3
    wceq
    @2
    @4
    cch
    cA
    @3
    cB
    ineq1
    eleq1d
    cB
    @5
    wceq
    @4
    @6
    cch
    cB
    @5
    @3
    ineq2
    eleq1d
    @3
    @5
    cA
    ifchhv
    cB
    ifchhv
    chincli
    dedth2h
end
