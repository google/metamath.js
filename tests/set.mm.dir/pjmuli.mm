include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "csm.mm"
include "co.mm"
include "cpjh.mm"
include "cfv.mm"
include "wceq.mm"
include "cc0.mm"
include "cif.mm"
include "c0v.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "ifhvhv0.mm"
include "0cn.mm"
include "elimel.mm"
include "pjmulii.mm"
include "dedth2h.mm"

theorem pjmuli
  let cA: class A
  let cB: class B
  let cH: class H
  assume pjadjt.1: |- H e. CH


  assert |- ( ( A e. CC /\ B e. ~H ) -> ( ( projh ` H ) ` ( A .h B ) ) = ( A .h ( ( projh ` H ) ` B ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    chil
    wcel
    #
    cA
    cB
    csm
    co
    #
    cH
    cpjh
    cfv
    #
    cfv
    #
    cA
    cB
    @3
    cfv
    #
    csm
    co
    #
    wceq
    @0
    cA
    cc0
    cif
    #
    cB
    csm
    co
    #
    @3
    cfv
    #
    @7
    @5
    csm
    co
    #
    wceq
    @7
    @1
    cB
    c0v
    cif
    #
    csm
    co
    #
    @3
    cfv
    #
    @7
    @11
    @3
    cfv
    #
    csm
    co
    #
    wceq
    cA
    cB
    cc0
    c0v
    cA
    @7
    wceq
    #
    @4
    @9
    @6
    @10
    @16
    @2
    @8
    @3
    cA
    @7
    cB
    csm
    oveq1
    fveq2d
    cA
    @7
    @5
    csm
    oveq1
    eqeq12d
    cB
    @11
    wceq
    #
    @9
    @13
    @10
    @15
    @17
    @8
    @12
    @3
    cB
    @11
    @7
    csm
    oveq2
    fveq2d
    @17
    @5
    @14
    @7
    csm
    cB
    @11
    @3
    fveq2
    oveq2d
    eqeq12d
    @11
    @7
    cH
    pjadjt.1
    cB
    ifhvhv0
    cA
    cc0
    cc
    0cn
    elimel
    pjmulii
    dedth2h
end
