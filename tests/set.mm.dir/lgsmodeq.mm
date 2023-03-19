include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "w3a.mm"
include "cmo.mm"
include "co.mm"
include "wceq.mm"
include "clgs.mm"
include "3anass.mm"
include "biimpri.mm"
include "3adant2.mm"
include "lgsmod.mm"
include "syl.mm"
include "oveq1.mm"
include "sylan9req.mm"
include "3adant1.mm"
include "adantr.mm"
include "eqtrd.mm"
include "ex.mm"

theorem lgsmodeq
  let cA: class A
  let cB: class B
  let cN: class N


  assert |- ( ( A e. ZZ /\ B e. ZZ /\ ( N e. NN /\ -. 2 || N ) ) -> ( ( A mod N ) = ( B mod N ) -> ( A /L N ) = ( B /L N ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    cN
    cn
    wcel
    #
    c2
    cN
    cdvds
    wbr
    wn
    #
    wa
    #
    w3a
    #
    cA
    cN
    cmo
    co
    #
    cB
    cN
    cmo
    co
    #
    wceq
    #
    cA
    cN
    clgs
    co
    #
    cB
    cN
    clgs
    co
    #
    wceq
    @5
    @8
    wa
    @9
    @7
    cN
    clgs
    co
    #
    @10
    @5
    @8
    @9
    @6
    cN
    clgs
    co
    #
    @11
    @5
    @0
    @2
    @3
    w3a
    #
    @12
    @9
    wceq
    @0
    @4
    @13
    @1
    @13
    @0
    @4
    wa
    @0
    @2
    @3
    3anass
    biimpri
    3adant2
    cA
    cN
    lgsmod
    syl
    @6
    @7
    cN
    clgs
    oveq1
    sylan9req
    @5
    @11
    @10
    wceq
    #
    @8
    @5
    @1
    @2
    @3
    w3a
    #
    @14
    @1
    @4
    @15
    @0
    @15
    @1
    @4
    wa
    @1
    @2
    @3
    3anass
    biimpri
    3adant1
    cB
    cN
    lgsmod
    syl
    adantr
    eqtrd
    ex
end
