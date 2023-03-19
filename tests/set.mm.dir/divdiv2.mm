include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "ax-1ne0.mm"
include "pm3.2i.mm"
include "divdivdiv.mm"
include "mpanl2.mm"
include "3impb.mm"
include "div1.mm"
include "3ad2ant1.mm"
include "oveq1d.mm"
include "mulid2.mm"
include "ad2antrl.mm"
include "3adant3.mm"
include "oveq2d.mm"
include "3eqtr3d.mm"

theorem divdiv2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ ( B e. CC /\ B =/= 0 ) /\ ( C e. CC /\ C =/= 0 ) ) -> ( A / ( B / C ) ) = ( ( A x. C ) / B ) )

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
    wa
    #
    cC
    cc
    wcel
    cC
    cc0
    wne
    wa
    #
    w3a
    #
    cA
    c1
    cdiv
    co
    #
    cB
    cC
    cdiv
    co
    #
    cdiv
    co
    #
    cA
    cC
    cmul
    co
    #
    c1
    cB
    cmul
    co
    #
    cdiv
    co
    #
    cA
    @7
    cdiv
    co
    @9
    cB
    cdiv
    co
    @0
    @3
    @4
    @8
    @11
    wceq
    #
    @0
    c1
    cc
    wcel
    #
    c1
    cc0
    wne
    #
    wa
    @3
    @4
    wa
    @12
    @13
    @14
    ax-1cn
    ax-1ne0
    pm3.2i
    cA
    c1
    cB
    cC
    divdivdiv
    mpanl2
    3impb
    @5
    @6
    cA
    @7
    cdiv
    @0
    @3
    @6
    cA
    wceq
    @4
    cA
    div1
    3ad2ant1
    oveq1d
    @5
    @10
    cB
    @9
    cdiv
    @0
    @3
    @10
    cB
    wceq
    #
    @4
    @1
    @15
    @0
    @2
    cB
    mulid2
    ad2antrl
    3adant3
    oveq2d
    3eqtr3d
end
