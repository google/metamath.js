include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "cmul.mm"
include "c2.mm"
include "cexp.mm"
include "wceq.mm"
include "2cn.mm"
include "mulcl.mm"
include "mpan.mm"
include "adantl.mm"
include "subadd23.mm"
include "mpd3an3.mm"
include "2times.mm"
include "oveq1d.mm"
include "pncan.mm"
include "anidms.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "subcl.mm"
include "adddird.mm"
include "eqtr3d.mm"
include "subsq.mm"
include "sqval.mm"
include "syl.mm"
include "3eqtr4d.mm"

theorem subsq2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( A ^ 2 ) - ( B ^ 2 ) ) = ( ( ( A - B ) ^ 2 ) + ( ( 2 x. B ) x. ( A - B ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    cB
    caddc
    co
    #
    cA
    cB
    cmin
    co
    #
    cmul
    co
    #
    @4
    @4
    cmul
    co
    #
    c2
    cB
    cmul
    co
    #
    @4
    cmul
    co
    #
    caddc
    co
    #
    cA
    c2
    cexp
    co
    cB
    c2
    cexp
    co
    cmin
    co
    @4
    c2
    cexp
    co
    #
    @8
    caddc
    co
    @2
    @4
    @7
    caddc
    co
    #
    @4
    cmul
    co
    @5
    @9
    @2
    @11
    @3
    @4
    cmul
    @2
    @11
    cA
    @7
    cB
    cmin
    co
    #
    caddc
    co
    #
    @3
    @0
    @1
    @7
    cc
    wcel
    #
    @11
    @13
    wceq
    @1
    @14
    @0
    c2
    cc
    wcel
    @1
    @14
    2cn
    c2
    cB
    mulcl
    mpan
    adantl
    #
    cA
    cB
    @7
    subadd23
    mpd3an3
    @2
    @12
    cB
    cA
    caddc
    @1
    @12
    cB
    wceq
    @0
    @1
    @12
    cB
    cB
    caddc
    co
    #
    cB
    cmin
    co
    #
    cB
    @1
    @7
    @16
    cB
    cmin
    cB
    2times
    oveq1d
    @1
    @17
    cB
    wceq
    cB
    cB
    pncan
    anidms
    eqtrd
    adantl
    oveq2d
    eqtrd
    oveq1d
    @2
    @4
    @7
    @4
    cA
    cB
    subcl
    #
    @15
    @18
    adddird
    eqtr3d
    cA
    cB
    subsq
    @2
    @10
    @6
    @8
    caddc
    @2
    @4
    cc
    wcel
    @10
    @6
    wceq
    @18
    @4
    sqval
    syl
    oveq1d
    3eqtr4d
end
