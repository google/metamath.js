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
include "ccot.mm"
include "ctan.mm"
include "wceq.mm"
include "wa.mm"
include "sincl.mm"
include "coscl.mm"
include "recdiv.mm"
include "sylanl1.mm"
include "sylanr1.mm"
include "3impdi.mm"
include "3com23.mm"
include "cotval.mm"
include "3adant3.mm"
include "oveq2d.mm"
include "tanval.mm"
include "3adant2.mm"
include "3eqtr4rd.mm"

theorem reccot
  let cA: class A
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. CC /\ ( sin ` A ) =/= 0 /\ ( cos ` A ) =/= 0 ) -> ( tan ` A ) = ( 1 / ( cot ` A ) ) )

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
    @3
    @1
    cdiv
    co
    #
    cdiv
    co
    #
    @1
    @3
    cdiv
    co
    #
    c1
    cA
    ccot
    cfv
    #
    cdiv
    co
    cA
    ctan
    cfv
    #
    @0
    @4
    @2
    @7
    @8
    wceq
    #
    @0
    @4
    @2
    @11
    @0
    @0
    @4
    wa
    @1
    cc
    wcel
    #
    @2
    @11
    cA
    sincl
    @0
    @3
    cc
    wcel
    @4
    @12
    @2
    wa
    @11
    cA
    coscl
    @3
    @1
    recdiv
    sylanl1
    sylanr1
    3impdi
    3com23
    @5
    @9
    @6
    c1
    cdiv
    @0
    @2
    @9
    @6
    wceq
    @4
    cA
    cotval
    3adant3
    oveq2d
    @0
    @4
    @10
    @8
    wceq
    @2
    cA
    tanval
    3adant2
    3eqtr4rd
end
