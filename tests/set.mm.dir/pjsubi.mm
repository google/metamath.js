include "chil.mm"
include "wcel.mm"
include "cmv.mm"
include "co.mm"
include "cpjh.mm"
include "cfv.mm"
include "wceq.mm"
include "c0v.mm"
include "cif.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "ifhvhv0.mm"
include "pjsubii.mm"
include "dedth2h.mm"

theorem pjsubi
  let cA: class A
  let cB: class B
  let cH: class H
  assume pjadjt.1: |- H e. CH


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( ( projh ` H ) ` ( A -h B ) ) = ( ( ( projh ` H ) ` A ) -h ( ( projh ` H ) ` B ) ) )

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
    cH
    cpjh
    cfv
    #
    cfv
    #
    cA
    @3
    cfv
    #
    cB
    @3
    cfv
    #
    cmv
    co
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
    @3
    cfv
    #
    @8
    @3
    cfv
    #
    @6
    cmv
    co
    #
    wceq
    @8
    @1
    cB
    c0v
    cif
    #
    cmv
    co
    #
    @3
    cfv
    #
    @11
    @13
    @3
    cfv
    #
    cmv
    co
    #
    wceq
    cA
    cB
    c0v
    c0v
    cA
    @8
    wceq
    #
    @4
    @10
    @7
    @12
    @18
    @2
    @9
    @3
    cA
    @8
    cB
    cmv
    oveq1
    fveq2d
    @18
    @5
    @11
    @6
    cmv
    cA
    @8
    @3
    fveq2
    oveq1d
    eqeq12d
    cB
    @13
    wceq
    #
    @10
    @15
    @12
    @17
    @19
    @9
    @14
    @3
    cB
    @13
    @8
    cmv
    oveq2
    fveq2d
    @19
    @6
    @16
    @11
    cmv
    cB
    @13
    @3
    fveq2
    oveq2d
    eqeq12d
    @8
    @13
    cH
    pjadjt.1
    cA
    ifhvhv0
    cB
    ifhvhv0
    pjsubii
    dedth2h
end
