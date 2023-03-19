include "chil.mm"
include "wcel.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "c0v.mm"
include "cif.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "bibi1d.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "bibi12d.mm"
include "eqeq2d.mm"
include "eqeq2.mm"
include "ifhvhv0.mm"
include "hvaddcani.mm"
include "dedth3h.mm"

theorem hvaddcan
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. ~H /\ B e. ~H /\ C e. ~H ) -> ( ( A +h B ) = ( A +h C ) <-> B = C ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    cC
    chil
    wcel
    #
    cA
    cB
    cva
    co
    #
    cA
    cC
    cva
    co
    #
    wceq
    #
    cB
    cC
    wceq
    #
    wb
    @0
    cA
    c0v
    cif
    #
    cB
    cva
    co
    #
    @7
    cC
    cva
    co
    #
    wceq
    #
    @6
    wb
    @7
    @1
    cB
    c0v
    cif
    #
    cva
    co
    #
    @9
    wceq
    #
    @11
    cC
    wceq
    #
    wb
    @12
    @7
    @2
    cC
    c0v
    cif
    #
    cva
    co
    #
    wceq
    #
    @11
    @15
    wceq
    #
    wb
    cA
    cB
    cC
    c0v
    c0v
    c0v
    cA
    @7
    wceq
    #
    @5
    @10
    @6
    @19
    @3
    @8
    @4
    @9
    cA
    @7
    cB
    cva
    oveq1
    cA
    @7
    cC
    cva
    oveq1
    eqeq12d
    bibi1d
    cB
    @11
    wceq
    #
    @10
    @13
    @6
    @14
    @20
    @8
    @12
    @9
    cB
    @11
    @7
    cva
    oveq2
    eqeq1d
    cB
    @11
    cC
    eqeq1
    bibi12d
    cC
    @15
    wceq
    #
    @13
    @17
    @14
    @18
    @21
    @9
    @16
    @12
    cC
    @15
    @7
    cva
    oveq2
    eqeq2d
    cC
    @15
    @11
    eqeq2
    bibi12d
    @7
    @11
    @15
    cA
    ifhvhv0
    cB
    ifhvhv0
    cC
    ifhvhv0
    hvaddcani
    dedth3h
end
