include "chil.mm"
include "wcel.mm"
include "cmv.mm"
include "co.mm"
include "cno.mm"
include "cfv.mm"
include "wceq.mm"
include "c0v.mm"
include "cif.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "ifhvhv0.mm"
include "normsubi.mm"
include "dedth2h.mm"

theorem normsub
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( normh ` ( A -h B ) ) = ( normh ` ( B -h A ) ) )

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
    cB
    cA
    cmv
    co
    #
    cno
    cfv
    #
    wceq
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
    cB
    @6
    cmv
    co
    #
    cno
    cfv
    #
    wceq
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
    @11
    @6
    cmv
    co
    #
    cno
    cfv
    #
    wceq
    cA
    cB
    c0v
    c0v
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
    cno
    cA
    @6
    cB
    cmv
    oveq1
    fveq2d
    @16
    @4
    @9
    cno
    cA
    @6
    cB
    cmv
    oveq2
    fveq2d
    eqeq12d
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
    cno
    cB
    @11
    @6
    cmv
    oveq2
    fveq2d
    @17
    @9
    @14
    cno
    cB
    @11
    @6
    cmv
    oveq1
    fveq2d
    eqeq12d
    @6
    @11
    cA
    ifhvhv0
    cB
    ifhvhv0
    normsubi
    dedth2h
end
