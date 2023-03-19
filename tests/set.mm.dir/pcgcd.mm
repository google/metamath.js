include "cprime.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cpc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cgcd.mm"
include "cif.mm"
include "wceq.mm"
include "wa.mm"
include "pcgcd1.mm"
include "iftrue.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "wn.mm"
include "gcdcom.mm"
include "3adant1.mm"
include "adantr.mm"
include "oveq2d.mm"
include "iffalse.mm"
include "cxr.mm"
include "wo.mm"
include "cq.mm"
include "zq.mm"
include "pcxcl.mm"
include "sylan2.mm"
include "3adant3.mm"
include "3adant2.mm"
include "xrletri.mm"
include "syl2anc.mm"
include "orcanai.mm"
include "3ancomb.mm"
include "sylanb.mm"
include "syldan.mm"
include "pm2.61dan.mm"

theorem pcgcd
  let cA: class A
  let cB: class B
  let cP: class P


  assert |- ( ( P e. Prime /\ A e. ZZ /\ B e. ZZ ) -> ( P pCnt ( A gcd B ) ) = if ( ( P pCnt A ) <_ ( P pCnt B ) , ( P pCnt A ) , ( P pCnt B ) ) )

  proof
    cP
    cprime
    wcel
    #
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    w3a
    #
    cP
    cA
    cpc
    co
    #
    cP
    cB
    cpc
    co
    #
    cle
    wbr
    #
    cP
    cA
    cB
    cgcd
    co
    #
    cpc
    co
    #
    @6
    @4
    @5
    cif
    #
    wceq
    @3
    @6
    wa
    @8
    @4
    @9
    cA
    cB
    cP
    pcgcd1
    @6
    @9
    @4
    wceq
    @3
    @6
    @4
    @5
    iftrue
    adantl
    eqtr4d
    @3
    @6
    wn
    #
    wa
    #
    @8
    cP
    cB
    cA
    cgcd
    co
    #
    cpc
    co
    #
    @9
    @11
    @7
    @12
    cP
    cpc
    @3
    @7
    @12
    wceq
    #
    @10
    @1
    @2
    @14
    @0
    cA
    cB
    gcdcom
    3adant1
    adantr
    oveq2d
    @11
    @9
    @5
    @13
    @10
    @9
    @5
    wceq
    @3
    @6
    @4
    @5
    iffalse
    adantl
    @3
    @10
    @5
    @4
    cle
    wbr
    #
    @13
    @5
    wceq
    #
    @3
    @6
    @15
    @3
    @4
    cxr
    wcel
    #
    @5
    cxr
    wcel
    #
    @6
    @15
    wo
    @0
    @1
    @17
    @2
    @1
    @0
    cA
    cq
    wcel
    @17
    cA
    zq
    cP
    cA
    pcxcl
    sylan2
    3adant3
    @0
    @2
    @18
    @1
    @2
    @0
    cB
    cq
    wcel
    @18
    cB
    zq
    cP
    cB
    pcxcl
    sylan2
    3adant2
    @4
    @5
    xrletri
    syl2anc
    orcanai
    @3
    @0
    @2
    @1
    w3a
    @15
    @16
    @0
    @1
    @2
    3ancomb
    cB
    cA
    cP
    pcgcd1
    sylanb
    syldan
    eqtr4d
    eqtr4d
    pm2.61dan
end
