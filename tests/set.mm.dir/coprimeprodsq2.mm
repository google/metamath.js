include "cz.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "cmul.mm"
include "cc.mm"
include "zcn.mm"
include "nn0cn.mm"
include "mulcom.mm"
include "syl2an.mm"
include "3adant3.mm"
include "adantr.mm"
include "eqeq2d.mm"
include "wi.mm"
include "simpl2.mm"
include "simpl1.mm"
include "simpl3.mm"
include "wb.mm"
include "nn0z.mm"
include "gcdcom.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "sylan2.mm"
include "biimpa.mm"
include "coprimeprodsq.mm"
include "syl31anc.mm"
include "sylbid.mm"

theorem coprimeprodsq2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. ZZ /\ B e. NN0 /\ C e. NN0 ) /\ ( ( A gcd B ) gcd C ) = 1 ) -> ( ( C ^ 2 ) = ( A x. B ) -> B = ( ( B gcd C ) ^ 2 ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cn0
    wcel
    #
    cC
    cn0
    wcel
    #
    w3a
    #
    cA
    cB
    cgcd
    co
    #
    cC
    cgcd
    co
    #
    c1
    wceq
    #
    wa
    #
    cC
    c2
    cexp
    co
    #
    cA
    cB
    cmul
    co
    #
    wceq
    @8
    cB
    cA
    cmul
    co
    #
    wceq
    #
    cB
    cB
    cC
    cgcd
    co
    c2
    cexp
    co
    wceq
    #
    @7
    @9
    @10
    @8
    @3
    @9
    @10
    wceq
    #
    @6
    @0
    @1
    @13
    @2
    @0
    cA
    cc
    wcel
    cB
    cc
    wcel
    @13
    @1
    cA
    zcn
    cB
    nn0cn
    cA
    cB
    mulcom
    syl2an
    3adant3
    adantr
    eqeq2d
    @7
    @1
    @0
    @2
    cB
    cA
    cgcd
    co
    #
    cC
    cgcd
    co
    #
    c1
    wceq
    #
    @11
    @12
    wi
    @0
    @1
    @2
    @6
    simpl2
    @0
    @1
    @2
    @6
    simpl1
    @0
    @1
    @2
    @6
    simpl3
    @3
    @6
    @16
    @0
    @1
    @6
    @16
    wb
    #
    @2
    @1
    @0
    cB
    cz
    wcel
    #
    @17
    cB
    nn0z
    @0
    @18
    wa
    #
    @5
    @15
    c1
    @19
    @4
    @14
    cC
    cgcd
    cA
    cB
    gcdcom
    oveq1d
    eqeq1d
    sylan2
    3adant3
    biimpa
    cB
    cA
    cC
    coprimeprodsq
    syl31anc
    sylbid
end
