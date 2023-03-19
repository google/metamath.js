include "cch.mm"
include "wcel.mm"
include "cin.mm"
include "ccv.mm"
include "wbr.mm"
include "chj.mm"
include "co.mm"
include "wb.mm"
include "chil.mm"
include "cif.mm"
include "wceq.mm"
include "ineq1.mm"
include "breq1d.mm"
include "id.mm"
include "oveq1.mm"
include "breq12d.mm"
include "bibi12d.mm"
include "ineq2.mm"
include "oveq2.mm"
include "breq2d.mm"
include "ifchhv.mm"
include "cvexchi.mm"
include "dedth2h.mm"

theorem cvexch
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( ( A i^i B ) <oH B <-> A <oH ( A vH B ) ) )

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
    cA
    cB
    chj
    co
    #
    ccv
    wbr
    #
    wb
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
    @6
    @6
    cB
    chj
    co
    #
    ccv
    wbr
    #
    wb
    @6
    @1
    cB
    chil
    cif
    #
    cin
    #
    @11
    ccv
    wbr
    #
    @6
    @6
    @11
    chj
    co
    #
    ccv
    wbr
    #
    wb
    cA
    cB
    chil
    chil
    cA
    @6
    wceq
    #
    @3
    @8
    @5
    @10
    @16
    @2
    @7
    cB
    ccv
    cA
    @6
    cB
    ineq1
    breq1d
    @16
    cA
    @6
    @4
    @9
    ccv
    @16
    id
    cA
    @6
    cB
    chj
    oveq1
    breq12d
    bibi12d
    cB
    @11
    wceq
    #
    @8
    @13
    @10
    @15
    @17
    @7
    @12
    cB
    @11
    ccv
    cB
    @11
    @6
    ineq2
    @17
    id
    breq12d
    @17
    @9
    @14
    @6
    ccv
    cB
    @11
    @6
    chj
    oveq2
    breq2d
    bibi12d
    @6
    @11
    cA
    ifchhv
    cB
    ifchhv
    cvexchi
    dedth2h
end
