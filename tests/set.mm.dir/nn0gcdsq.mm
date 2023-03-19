include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "cgcd.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "elnn0.mm"
include "sqgcd.mm"
include "wa.mm"
include "cabs.mm"
include "cfv.mm"
include "cc.mm"
include "nncn.mm"
include "abssq.mm"
include "syl.mm"
include "cz.mm"
include "nnz.mm"
include "gcd0id.mm"
include "oveq1d.mm"
include "sq0.mm"
include "a1i.mm"
include "zsqcl.mm"
include "3syl.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"
include "adantl.mm"
include "wb.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "adantr.mm"
include "mpbird.mm"
include "gcdid0.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "gcd0val.mm"
include "oveq1i.mm"
include "oveq12i.mm"
include "eqtri.mm"
include "3eqtr4i.mm"
include "oveq12.mm"
include "oveqan12d.mm"
include "3eqtr4a.mm"
include "ccase.mm"
include "syl2anb.mm"

theorem nn0gcdsq
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let cC: class C
  let vx: setvar x


  assert |- ( ( A e. NN0 /\ B e. NN0 ) -> ( ( A gcd B ) ^ 2 ) = ( ( A ^ 2 ) gcd ( B ^ 2 ) ) )

  proof
    cA
    cn0
    wcel
    cA
    cn
    wcel
    #
    cA
    cc0
    wceq
    #
    wo
    cB
    cn
    wcel
    #
    cB
    cc0
    wceq
    #
    wo
    cA
    cB
    cgcd
    co
    #
    c2
    cexp
    co
    #
    cA
    c2
    cexp
    co
    #
    cB
    c2
    cexp
    co
    #
    cgcd
    co
    #
    wceq
    #
    cB
    cn0
    wcel
    cA
    elnn0
    cB
    elnn0
    @0
    @2
    @1
    @3
    @9
    cA
    cB
    sqgcd
    @1
    @2
    wa
    @9
    cc0
    cB
    cgcd
    co
    #
    c2
    cexp
    co
    #
    cc0
    c2
    cexp
    co
    #
    @7
    cgcd
    co
    #
    wceq
    #
    @2
    @14
    @1
    @2
    cB
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    @7
    cabs
    cfv
    #
    @11
    @13
    @2
    cB
    cc
    wcel
    @16
    @17
    wceq
    cB
    nncn
    cB
    abssq
    syl
    @2
    @10
    @15
    c2
    cexp
    @2
    cB
    cz
    wcel
    #
    @10
    @15
    wceq
    cB
    nnz
    #
    cB
    gcd0id
    syl
    oveq1d
    @2
    @13
    cc0
    @7
    cgcd
    co
    #
    @17
    @2
    @12
    cc0
    @7
    cgcd
    @12
    cc0
    wceq
    #
    @2
    sq0
    a1i
    oveq1d
    @2
    @18
    @7
    cz
    wcel
    @20
    @17
    wceq
    @19
    cB
    zsqcl
    @7
    gcd0id
    3syl
    eqtrd
    3eqtr4d
    adantl
    @1
    @9
    @14
    wb
    @2
    @1
    @5
    @11
    @8
    @13
    @1
    @4
    @10
    c2
    cexp
    cA
    cc0
    cB
    cgcd
    oveq1
    oveq1d
    @1
    @6
    @12
    @7
    cgcd
    cA
    cc0
    c2
    cexp
    oveq1
    #
    oveq1d
    eqeq12d
    adantr
    mpbird
    @0
    @3
    wa
    @9
    cA
    cc0
    cgcd
    co
    #
    c2
    cexp
    co
    #
    @6
    @12
    cgcd
    co
    #
    wceq
    #
    @0
    @26
    @3
    @0
    cA
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    @6
    cabs
    cfv
    #
    @24
    @25
    @0
    cA
    cc
    wcel
    @28
    @29
    wceq
    cA
    nncn
    cA
    abssq
    syl
    @0
    @23
    @27
    c2
    cexp
    @0
    cA
    cz
    wcel
    #
    @23
    @27
    wceq
    cA
    nnz
    #
    cA
    gcdid0
    syl
    oveq1d
    @0
    @25
    @6
    cc0
    cgcd
    co
    #
    @29
    @0
    @12
    cc0
    @6
    cgcd
    @21
    @0
    sq0
    a1i
    oveq2d
    @0
    @30
    @6
    cz
    wcel
    @32
    @29
    wceq
    @31
    cA
    zsqcl
    @6
    gcdid0
    3syl
    eqtrd
    3eqtr4d
    adantr
    @3
    @9
    @26
    wb
    @0
    @3
    @5
    @24
    @8
    @25
    @3
    @4
    @23
    c2
    cexp
    cB
    cc0
    cA
    cgcd
    oveq2
    oveq1d
    @3
    @7
    @12
    @6
    cgcd
    cB
    cc0
    c2
    cexp
    oveq1
    #
    oveq2d
    eqeq12d
    adantl
    mpbird
    @1
    @3
    wa
    #
    cc0
    cc0
    cgcd
    co
    #
    c2
    cexp
    co
    #
    @12
    @12
    cgcd
    co
    #
    @5
    @8
    @12
    cc0
    @36
    @37
    sq0
    @35
    cc0
    c2
    cexp
    gcd0val
    oveq1i
    @37
    @35
    cc0
    @12
    cc0
    @12
    cc0
    cgcd
    sq0
    sq0
    oveq12i
    gcd0val
    eqtri
    3eqtr4i
    @34
    @4
    @35
    c2
    cexp
    cA
    cc0
    cB
    cc0
    cgcd
    oveq12
    oveq1d
    @1
    @3
    @6
    @12
    @7
    @12
    cgcd
    @22
    @33
    oveqan12d
    3eqtr4a
    ccase
    syl2anb
end
