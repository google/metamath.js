include "chil.mm"
include "wcel.mm"
include "cmv.mm"
include "co.mm"
include "c0v.mm"
include "wceq.mm"
include "wb.mm"
include "cif.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "bibi12d.mm"
include "oveq2.mm"
include "eqeq2.mm"
include "ifhvhv0.mm"
include "hvsubeq0i.mm"
include "dedth2h.mm"

theorem hvsubeq0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( ( A -h B ) = 0h <-> A = B ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    cA
    cB
    cmv
    co
    #
    c0v
    wceq
    #
    cA
    cB
    wceq
    #
    wb
    @0
    cA
    c0v
    cif
    #
    cB
    cmv
    co
    #
    c0v
    wceq
    #
    @5
    cB
    wceq
    #
    wb
    @5
    @1
    cB
    c0v
    cif
    #
    cmv
    co
    #
    c0v
    wceq
    #
    @5
    @9
    wceq
    #
    wb
    cA
    cB
    c0v
    c0v
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
    c0v
    cA
    @5
    cB
    cmv
    oveq1
    eqeq1d
    cA
    @5
    cB
    eqeq1
    bibi12d
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
    c0v
    cB
    @9
    @5
    cmv
    oveq2
    eqeq1d
    cB
    @9
    @5
    eqeq2
    bibi12d
    @5
    @9
    cA
    ifhvhv0
    cB
    ifhvhv0
    hvsubeq0i
    dedth2h
end
