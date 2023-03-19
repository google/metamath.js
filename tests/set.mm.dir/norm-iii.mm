include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "csm.mm"
include "co.mm"
include "cno.mm"
include "cfv.mm"
include "cabs.mm"
include "cmul.mm"
include "wceq.mm"
include "cc0.mm"
include "cif.mm"
include "c0v.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "0cn.mm"
include "elimel.mm"
include "ifhvhv0.mm"
include "norm-iii-i.mm"
include "dedth2h.mm"

theorem norm-iii
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. ~H ) -> ( normh ` ( A .h B ) ) = ( ( abs ` A ) x. ( normh ` B ) ) )

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
    cno
    cfv
    #
    cA
    cabs
    cfv
    #
    cB
    cno
    cfv
    #
    cmul
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
    cno
    cfv
    #
    @7
    cabs
    cfv
    #
    @5
    cmul
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
    cno
    cfv
    #
    @10
    @12
    cno
    cfv
    #
    cmul
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
    @3
    @9
    @6
    @11
    @17
    @2
    @8
    cno
    cA
    @7
    cB
    csm
    oveq1
    fveq2d
    @17
    @4
    @10
    @5
    cmul
    cA
    @7
    cabs
    fveq2
    oveq1d
    eqeq12d
    cB
    @12
    wceq
    #
    @9
    @14
    @11
    @16
    @18
    @8
    @13
    cno
    cB
    @12
    @7
    csm
    oveq2
    fveq2d
    @18
    @5
    @15
    @10
    cmul
    cB
    @12
    cno
    fveq2
    oveq2d
    eqeq12d
    @7
    @12
    cA
    cc0
    cc
    0cn
    elimel
    cB
    ifhvhv0
    norm-iii-i
    dedth2h
end
