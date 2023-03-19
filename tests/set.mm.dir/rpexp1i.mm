include "cz.mm"
include "wcel.mm"
include "cn0.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "cexp.mm"
include "wi.mm"
include "wa.mm"
include "cn.mm"
include "cc0.mm"
include "wo.mm"
include "elnn0.mm"
include "w3a.mm"
include "rpexp.mm"
include "biimprd.mm"
include "3expa.mm"
include "simpr.mm"
include "oveq2d.mm"
include "cc.mm"
include "zcn.mm"
include "ad2antrr.mm"
include "exp0d.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "1gcd.mm"
include "ad2antlr.mm"
include "a1d.mm"
include "jaodan.mm"
include "sylan2b.mm"
include "3impa.mm"

theorem rpexp1i
  let cA: class A
  let cB: class B
  let cM: class M


  assert |- ( ( A e. ZZ /\ B e. ZZ /\ M e. NN0 ) -> ( ( A gcd B ) = 1 -> ( ( A ^ M ) gcd B ) = 1 ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    cM
    cn0
    wcel
    #
    cA
    cB
    cgcd
    co
    c1
    wceq
    #
    cA
    cM
    cexp
    co
    #
    cB
    cgcd
    co
    #
    c1
    wceq
    #
    wi
    #
    @2
    @0
    @1
    wa
    #
    cM
    cn
    wcel
    #
    cM
    cc0
    wceq
    #
    wo
    @7
    cM
    elnn0
    @8
    @9
    @7
    @10
    @0
    @1
    @9
    @7
    @0
    @1
    @9
    w3a
    @6
    @3
    cA
    cB
    cM
    rpexp
    biimprd
    3expa
    @8
    @10
    wa
    #
    @6
    @3
    @11
    @5
    c1
    cB
    cgcd
    co
    #
    c1
    @11
    @4
    c1
    cB
    cgcd
    @11
    @4
    cA
    cc0
    cexp
    co
    c1
    @11
    cM
    cc0
    cA
    cexp
    @8
    @10
    simpr
    oveq2d
    @11
    cA
    @0
    cA
    cc
    wcel
    @1
    @10
    cA
    zcn
    ad2antrr
    exp0d
    eqtrd
    oveq1d
    @1
    @12
    c1
    wceq
    @0
    @10
    cB
    1gcd
    ad2antlr
    eqtrd
    a1d
    jaodan
    sylan2b
    3impa
end
