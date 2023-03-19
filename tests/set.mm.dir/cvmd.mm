include "cch.mm"
include "wcel.mm"
include "cin.mm"
include "ccv.mm"
include "wbr.mm"
include "cmd.mm"
include "wi.mm"
include "chil.mm"
include "cif.mm"
include "wceq.mm"
include "ineq1.mm"
include "breq1d.mm"
include "breq1.mm"
include "imbi12d.mm"
include "ineq2.mm"
include "id.mm"
include "breq12d.mm"
include "breq2.mm"
include "ifchhv.mm"
include "cvmdi.mm"
include "dedth2h.mm"
include "3impia.mm"

theorem cvmd
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH /\ ( A i^i B ) <oH B ) -> A MH B )

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
    cB
    ccv
    wbr
    #
    cA
    cB
    cmd
    wbr
    #
    @0
    @1
    @3
    @4
    wi
    @0
    cA
    chil
    cif
    #
    cB
    cin
    #
    cB
    ccv
    wbr
    #
    @5
    cB
    cmd
    wbr
    #
    wi
    @5
    @1
    cB
    chil
    cif
    #
    cin
    #
    @9
    ccv
    wbr
    #
    @5
    @9
    cmd
    wbr
    #
    wi
    cA
    cB
    chil
    chil
    cA
    @5
    wceq
    #
    @3
    @7
    @4
    @8
    @13
    @2
    @6
    cB
    ccv
    cA
    @5
    cB
    ineq1
    breq1d
    cA
    @5
    cB
    cmd
    breq1
    imbi12d
    cB
    @9
    wceq
    #
    @7
    @11
    @8
    @12
    @14
    @6
    @10
    cB
    @9
    ccv
    cB
    @9
    @5
    ineq2
    @14
    id
    breq12d
    cB
    @9
    @5
    cmd
    breq2
    imbi12d
    @5
    @9
    cA
    ifchhv
    cB
    ifchhv
    cvmdi
    dedth2h
    3impia
end
