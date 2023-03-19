include "cn.mm"
include "wcel.mm"
include "w3a.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "cexp.mm"
include "wa.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "nnnn0d.mm"
include "nnexpcld.mm"
include "3jca.mm"
include "cz.mm"
include "nnzd.mm"
include "gcdcom.mm"
include "syl2anc.mm"
include "nnz.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "eqeq1d.mm"
include "biimpa.mm"
include "rplpwr.mm"
include "sylc.mm"
include "eqtrd.mm"
include "ex.mm"

theorem rppwr
  let cA: class A
  let cB: class B
  let cN: class N


  assert |- ( ( A e. NN /\ B e. NN /\ N e. NN ) -> ( ( A gcd B ) = 1 -> ( ( A ^ N ) gcd ( B ^ N ) ) = 1 ) )

  proof
    cA
    cn
    wcel
    #
    cB
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    w3a
    #
    cA
    cB
    cgcd
    co
    #
    c1
    wceq
    #
    cA
    cN
    cexp
    co
    cB
    cN
    cexp
    co
    #
    cgcd
    co
    c1
    wceq
    #
    @3
    @5
    wa
    #
    @0
    @6
    cn
    wcel
    #
    @2
    w3a
    cA
    @6
    cgcd
    co
    #
    c1
    wceq
    @7
    @8
    @0
    @9
    @2
    @0
    @1
    @2
    @5
    simpl1
    #
    @8
    cB
    cN
    @0
    @1
    @2
    @5
    simpl2
    #
    @8
    cN
    @0
    @1
    @2
    @5
    simpl3
    #
    nnnn0d
    nnexpcld
    #
    @13
    3jca
    @8
    @10
    @6
    cA
    cgcd
    co
    #
    c1
    @8
    cA
    cz
    wcel
    #
    @6
    cz
    wcel
    @10
    @15
    wceq
    @8
    cA
    @11
    nnzd
    @8
    @6
    @14
    nnzd
    cA
    @6
    gcdcom
    syl2anc
    @8
    @1
    @0
    @2
    w3a
    cB
    cA
    cgcd
    co
    #
    c1
    wceq
    #
    @15
    c1
    wceq
    @8
    @1
    @0
    @2
    @12
    @11
    @13
    3jca
    @3
    @5
    @18
    @3
    @4
    @17
    c1
    @3
    @16
    cB
    cz
    wcel
    #
    @4
    @17
    wceq
    @0
    @1
    @16
    @2
    cA
    nnz
    3ad2ant1
    @1
    @0
    @19
    @2
    cB
    nnz
    3ad2ant2
    cA
    cB
    gcdcom
    syl2anc
    eqeq1d
    biimpa
    cB
    cA
    cN
    rplpwr
    sylc
    eqtrd
    cA
    @6
    cN
    rplpwr
    sylc
    ex
end
