include "csh.mm"
include "wcel.mm"
include "cin.mm"
include "chil.mm"
include "cif.mm"
include "wceq.mm"
include "ineq1.mm"
include "eleq1d.mm"
include "ineq2.mm"
include "helsh.mm"
include "elimel.mm"
include "shincli.mm"
include "dedth2h.mm"

theorem shincl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. SH /\ B e. SH ) -> ( A i^i B ) e. SH )

  proof
    cA
    csh
    wcel
    #
    cB
    csh
    wcel
    #
    cA
    cB
    cin
    #
    csh
    wcel
    @0
    cA
    chil
    cif
    #
    cB
    cin
    #
    csh
    wcel
    @3
    @1
    cB
    chil
    cif
    #
    cin
    #
    csh
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
    csh
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
    csh
    cB
    @5
    @3
    ineq2
    eleq1d
    @3
    @5
    cA
    chil
    csh
    helsh
    elimel
    cB
    chil
    csh
    helsh
    elimel
    shincli
    dedth2h
end
