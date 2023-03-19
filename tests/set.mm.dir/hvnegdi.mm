include "chil.mm"
include "wcel.mm"
include "c1.mm"
include "cneg.mm"
include "cmv.mm"
include "co.mm"
include "csm.mm"
include "wceq.mm"
include "c0v.mm"
include "cif.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "ifhvhv0.mm"
include "hvnegdii.mm"
include "dedth2h.mm"

theorem hvnegdi
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( -u 1 .h ( A -h B ) ) = ( B -h A ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    c1
    cneg
    #
    cA
    cB
    cmv
    co
    #
    csm
    co
    #
    cB
    cA
    cmv
    co
    #
    wceq
    @2
    @0
    cA
    c0v
    cif
    #
    cB
    cmv
    co
    #
    csm
    co
    #
    cB
    @6
    cmv
    co
    #
    wceq
    @2
    @6
    @1
    cB
    c0v
    cif
    #
    cmv
    co
    #
    csm
    co
    #
    @10
    @6
    cmv
    co
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
    @4
    @8
    @5
    @9
    @14
    @3
    @7
    @2
    csm
    cA
    @6
    cB
    cmv
    oveq1
    oveq2d
    cA
    @6
    cB
    cmv
    oveq2
    eqeq12d
    cB
    @10
    wceq
    #
    @8
    @12
    @9
    @13
    @15
    @7
    @11
    @2
    csm
    cB
    @10
    @6
    cmv
    oveq2
    oveq2d
    cB
    @10
    @6
    cmv
    oveq1
    eqeq12d
    @6
    @10
    cA
    ifhvhv0
    cB
    ifhvhv0
    hvnegdii
    dedth2h
end
