include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "cmin.mm"
include "cdiv.mm"
include "wceq.mm"
include "simp3l.mm"
include "simp2.mm"
include "mulcld.mm"
include "divsubdir.mm"
include "syld3an2.mm"
include "simprl.mm"
include "simpl.mm"
include "simpr.mm"
include "div23.mm"
include "syl3anc.mm"
include "c1.mm"
include "divid.mm"
include "oveq1d.mm"
include "mulid2.mm"
include "sylan9eqr.mm"
include "eqtrd.mm"
include "3adant1.mm"
include "oveq2d.mm"

theorem subdivcomb2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ ( C e. CC /\ C =/= 0 ) ) -> ( ( A - ( C x. B ) ) / C ) = ( ( A / C ) - B ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
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
    #
    cA
    cC
    cB
    cmul
    co
    #
    cmin
    co
    cC
    cdiv
    co
    #
    cA
    cC
    cdiv
    co
    #
    @6
    cC
    cdiv
    co
    #
    cmin
    co
    #
    @8
    cB
    cmin
    co
    @0
    @6
    cc
    wcel
    @1
    @4
    @7
    @10
    wceq
    @5
    cC
    cB
    @0
    @1
    @2
    @3
    simp3l
    @0
    @1
    @4
    simp2
    mulcld
    cA
    @6
    cC
    divsubdir
    syld3an2
    @5
    @9
    cB
    @8
    cmin
    @1
    @4
    @9
    cB
    wceq
    @0
    @1
    @4
    wa
    #
    @9
    cC
    cC
    cdiv
    co
    #
    cB
    cmul
    co
    #
    cB
    @11
    @2
    @1
    @4
    @9
    @13
    wceq
    @1
    @2
    @3
    simprl
    @1
    @4
    simpl
    @1
    @4
    simpr
    cC
    cB
    cC
    div23
    syl3anc
    @4
    @1
    @13
    c1
    cB
    cmul
    co
    cB
    @4
    @12
    c1
    cB
    cmul
    cC
    divid
    oveq1d
    cB
    mulid2
    sylan9eqr
    eqtrd
    3adant1
    oveq2d
    eqtrd
end
