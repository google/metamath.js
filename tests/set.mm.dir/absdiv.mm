include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "cmul.mm"
include "cr.mm"
include "divcl.mm"
include "abscl.mm"
include "syl.mm"
include "recnd.mm"
include "crp.mm"
include "absrpcl.mm"
include "3adant1.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "divcan4d.mm"
include "wceq.mm"
include "simp2.mm"
include "absmul.mm"
include "syl2anc.mm"
include "divcan1.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "oveq1d.mm"

theorem absdiv
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC /\ B =/= 0 ) -> ( abs ` ( A / B ) ) = ( ( abs ` A ) / ( abs ` B ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    w3a
    #
    cA
    cB
    cdiv
    co
    #
    cabs
    cfv
    #
    cB
    cabs
    cfv
    #
    cmul
    co
    #
    @6
    cdiv
    co
    @5
    cA
    cabs
    cfv
    #
    @6
    cdiv
    co
    @3
    @5
    @6
    @3
    @5
    @3
    @4
    cc
    wcel
    #
    @5
    cr
    wcel
    cA
    cB
    divcl
    #
    @4
    abscl
    syl
    recnd
    @3
    @6
    @1
    @2
    @6
    crp
    wcel
    @0
    cB
    absrpcl
    3adant1
    #
    rpcnd
    @3
    @6
    @11
    rpne0d
    divcan4d
    @3
    @7
    @8
    @6
    cdiv
    @3
    @4
    cB
    cmul
    co
    #
    cabs
    cfv
    #
    @7
    @8
    @3
    @9
    @1
    @13
    @7
    wceq
    @10
    @0
    @1
    @2
    simp2
    @4
    cB
    absmul
    syl2anc
    @3
    @12
    cA
    cabs
    cA
    cB
    divcan1
    fveq2d
    eqtr3d
    oveq1d
    eqtr3d
end
