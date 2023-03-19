include "chil.mm"
include "wcel.mm"
include "cmv.mm"
include "co.mm"
include "wceq.mm"
include "cva.mm"
include "wb.mm"
include "c0v.mm"
include "cif.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "eqeq2.mm"
include "bibi12d.mm"
include "oveq2.mm"
include "ifhvhv0.mm"
include "hvsubaddi.mm"
include "dedth3h.mm"

theorem hvsubadd
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. ~H /\ B e. ~H /\ C e. ~H ) -> ( ( A -h B ) = C <-> ( B +h C ) = A ) )

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
    cmv
    co
    #
    cC
    wceq
    #
    cB
    cC
    cva
    co
    #
    cA
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
    cC
    wceq
    #
    @5
    @7
    wceq
    #
    wb
    @7
    @1
    cB
    c0v
    cif
    #
    cmv
    co
    #
    cC
    wceq
    #
    @11
    cC
    cva
    co
    #
    @7
    wceq
    #
    wb
    @12
    @2
    cC
    c0v
    cif
    #
    wceq
    #
    @11
    @16
    cva
    co
    #
    @7
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
    @4
    @9
    @6
    @10
    @20
    @3
    @8
    cC
    cA
    @7
    cB
    cmv
    oveq1
    eqeq1d
    cA
    @7
    @5
    eqeq2
    bibi12d
    cB
    @11
    wceq
    #
    @9
    @13
    @10
    @15
    @21
    @8
    @12
    cC
    cB
    @11
    @7
    cmv
    oveq2
    eqeq1d
    @21
    @5
    @14
    @7
    cB
    @11
    cC
    cva
    oveq1
    eqeq1d
    bibi12d
    cC
    @16
    wceq
    #
    @13
    @17
    @15
    @19
    cC
    @16
    @12
    eqeq2
    @22
    @14
    @18
    @7
    cC
    @16
    @11
    cva
    oveq2
    eqeq1d
    bibi12d
    @7
    @11
    @16
    cA
    ifhvhv0
    cB
    ifhvhv0
    cC
    ifhvhv0
    hvsubaddi
    dedth3h
end
