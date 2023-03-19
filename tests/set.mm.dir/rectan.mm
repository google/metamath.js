include "cc.mm"
include "wcel.mm"
include "csin.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "ccos.mm"
include "w3a.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "ctan.mm"
include "ccot.mm"
include "wceq.mm"
include "wa.mm"
include "coscl.mm"
include "sincl.mm"
include "recdiv.mm"
include "sylanl1.mm"
include "sylanr1.mm"
include "3impdi.mm"
include "tanval.mm"
include "3adant2.mm"
include "oveq2d.mm"
include "cotval.mm"
include "3adant3.mm"
include "3eqtr4rd.mm"

theorem rectan
  let cA: class A
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. CC /\ ( sin ` A ) =/= 0 /\ ( cos ` A ) =/= 0 ) -> ( cot ` A ) = ( 1 / ( tan ` A ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    csin
    cfv
    #
    cc0
    wne
    #
    cA
    ccos
    cfv
    #
    cc0
    wne
    #
    w3a
    #
    c1
    @1
    @3
    cdiv
    co
    #
    cdiv
    co
    #
    @3
    @1
    cdiv
    co
    #
    c1
    cA
    ctan
    cfv
    #
    cdiv
    co
    cA
    ccot
    cfv
    #
    @0
    @2
    @4
    @7
    @8
    wceq
    #
    @0
    @0
    @2
    wa
    @3
    cc
    wcel
    #
    @4
    @11
    cA
    coscl
    @0
    @1
    cc
    wcel
    @2
    @12
    @4
    wa
    @11
    cA
    sincl
    @1
    @3
    recdiv
    sylanl1
    sylanr1
    3impdi
    @5
    @9
    @6
    c1
    cdiv
    @0
    @4
    @9
    @6
    wceq
    @2
    cA
    tanval
    3adant2
    oveq2d
    @0
    @2
    @10
    @8
    wceq
    @4
    cA
    cotval
    3adant3
    3eqtr4rd
end
