include "chil.mm"
include "wcel.mm"
include "cmv.mm"
include "co.mm"
include "cno.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "c0v.mm"
include "cif.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "bibi12d.mm"
include "oveq2.mm"
include "eqeq2.mm"
include "ifhvhv0.mm"
include "normsub0i.mm"
include "dedth2h.mm"

theorem normsub0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( ( normh ` ( A -h B ) ) = 0 <-> A = B ) )

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
    cno
    cfv
    #
    cc0
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
    cno
    cfv
    #
    cc0
    wceq
    #
    @6
    cB
    wceq
    #
    wb
    @6
    @1
    cB
    c0v
    cif
    #
    cmv
    co
    #
    cno
    cfv
    #
    cc0
    wceq
    #
    @6
    @11
    wceq
    #
    wb
    cA
    cB
    c0v
    c0v
    cA
    @6
    wceq
    #
    @4
    @9
    @5
    @10
    @16
    @3
    @8
    cc0
    @16
    @2
    @7
    cno
    cA
    @6
    cB
    cmv
    oveq1
    fveq2d
    eqeq1d
    cA
    @6
    cB
    eqeq1
    bibi12d
    cB
    @11
    wceq
    #
    @9
    @14
    @10
    @15
    @17
    @8
    @13
    cc0
    @17
    @7
    @12
    cno
    cB
    @11
    @6
    cmv
    oveq2
    fveq2d
    eqeq1d
    cB
    @11
    @6
    eqeq2
    bibi12d
    @6
    @11
    cA
    ifhvhv0
    cB
    ifhvhv0
    normsub0i
    dedth2h
end
