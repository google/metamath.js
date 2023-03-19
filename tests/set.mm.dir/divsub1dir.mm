include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "wa.mm"
include "wceq.mm"
include "3simpc.mm"
include "divid.mm"
include "syl.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "divsubdir.mm"
include "syld3an3.mm"
include "eqtr4d.mm"

theorem divsub1dir
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. CC /\ B e. CC /\ B =/= 0 ) -> ( ( A / B ) - 1 ) = ( ( A - B ) / B ) )

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
    c1
    cmin
    co
    @4
    cB
    cB
    cdiv
    co
    #
    cmin
    co
    #
    cA
    cB
    cmin
    co
    cB
    cdiv
    co
    #
    @3
    c1
    @5
    @4
    cmin
    @3
    @5
    c1
    @3
    @1
    @2
    wa
    #
    @5
    c1
    wceq
    @0
    @1
    @2
    3simpc
    #
    cB
    divid
    syl
    eqcomd
    oveq2d
    @0
    @1
    @2
    @8
    @7
    @6
    wceq
    @9
    cA
    cB
    cB
    divsubdir
    syld3an3
    eqtr4d
end
