include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "cmul.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "ax-1ne0.mm"
include "pm3.2i.mm"
include "divdivdiv.mm"
include "mpanr2.mm"
include "3impa.mm"
include "div1.mm"
include "oveq2d.mm"
include "ad2antrl.mm"
include "3adant1.mm"
include "mulid1.mm"
include "oveq1d.mm"
include "3ad2ant1.mm"
include "3eqtr3d.mm"

theorem divdiv1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ ( B e. CC /\ B =/= 0 ) /\ ( C e. CC /\ C =/= 0 ) ) -> ( ( A / B ) / C ) = ( A / ( B x. C ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    cB
    cc0
    wne
    wa
    #
    cC
    cc
    wcel
    #
    cC
    cc0
    wne
    #
    wa
    #
    w3a
    cA
    cB
    cdiv
    co
    #
    cC
    c1
    cdiv
    co
    #
    cdiv
    co
    #
    cA
    c1
    cmul
    co
    #
    cB
    cC
    cmul
    co
    #
    cdiv
    co
    #
    @5
    cC
    cdiv
    co
    #
    cA
    @9
    cdiv
    co
    #
    @0
    @1
    @4
    @7
    @10
    wceq
    #
    @0
    @1
    wa
    @4
    c1
    cc
    wcel
    #
    c1
    cc0
    wne
    #
    wa
    @13
    @14
    @15
    ax-1cn
    ax-1ne0
    pm3.2i
    cA
    cB
    cC
    c1
    divdivdiv
    mpanr2
    3impa
    @1
    @4
    @7
    @11
    wceq
    #
    @0
    @2
    @16
    @1
    @3
    @2
    @6
    cC
    @5
    cdiv
    cC
    div1
    oveq2d
    ad2antrl
    3adant1
    @0
    @1
    @10
    @12
    wceq
    @4
    @0
    @8
    cA
    @9
    cdiv
    cA
    mulid1
    oveq1d
    3ad2ant1
    3eqtr3d
end
