include "cz.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "w3a.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "cexp.mm"
include "wi.mm"
include "rpexp1i.mm"
include "3adant3r.mm"
include "simp2.mm"
include "simp1.mm"
include "simp3l.mm"
include "zexpcl.mm"
include "syl2anc.mm"
include "simp3r.mm"
include "syl3anc.mm"
include "gcdcom.mm"
include "eqeq1d.mm"
include "3imtr4d.mm"
include "syld.mm"

theorem rpexp12i
  let cA: class A
  let cB: class B
  let cM: class M
  let cN: class N


  assert |- ( ( A e. ZZ /\ B e. ZZ /\ ( M e. NN0 /\ N e. NN0 ) ) -> ( ( A gcd B ) = 1 -> ( ( A ^ M ) gcd ( B ^ N ) ) = 1 ) )

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
    cN
    cn0
    wcel
    #
    wa
    #
    w3a
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
    @7
    cB
    cN
    cexp
    co
    #
    cgcd
    co
    #
    c1
    wceq
    #
    @0
    @1
    @2
    @6
    @9
    wi
    @3
    cA
    cB
    cM
    rpexp1i
    3adant3r
    @5
    cB
    @7
    cgcd
    co
    #
    c1
    wceq
    #
    @10
    @7
    cgcd
    co
    #
    c1
    wceq
    #
    @9
    @12
    @5
    @1
    @7
    cz
    wcel
    #
    @3
    @14
    @16
    wi
    @0
    @1
    @4
    simp2
    #
    @5
    @0
    @2
    @17
    @0
    @1
    @4
    simp1
    @0
    @1
    @2
    @3
    simp3l
    cA
    cM
    zexpcl
    syl2anc
    #
    @0
    @1
    @2
    @3
    simp3r
    #
    cB
    @7
    cN
    rpexp1i
    syl3anc
    @5
    @8
    @13
    c1
    @5
    @17
    @1
    @8
    @13
    wceq
    @19
    @18
    @7
    cB
    gcdcom
    syl2anc
    eqeq1d
    @5
    @11
    @15
    c1
    @5
    @17
    @10
    cz
    wcel
    #
    @11
    @15
    wceq
    @19
    @5
    @1
    @3
    @21
    @18
    @20
    cB
    cN
    zexpcl
    syl2anc
    @7
    @10
    gcdcom
    syl2anc
    eqeq1d
    3imtr4d
    syld
end
