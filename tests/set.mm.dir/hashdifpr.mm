include "cfn.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "cpr.mm"
include "cdif.mm"
include "chash.mm"
include "cfv.mm"
include "csn.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "wceq.mm"
include "difpr.mm"
include "a1i.mm"
include "fveq2d.mm"
include "diffi.mm"
include "necom.mm"
include "biimpi.mm"
include "anim2i.mm"
include "3adant1.mm"
include "adantl.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "hashdifsn.mm"
include "syl2an2r.mm"
include "3ad2antr1.mm"
include "oveq1d.mm"
include "cc.mm"
include "hashcl.mm"
include "nn0cnd.mm"
include "sub1m1.mm"
include "syl.mm"
include "adantr.mm"
include "eqtrd.mm"
include "3eqtrd.mm"

theorem hashdifpr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. Fin /\ ( B e. A /\ C e. A /\ B =/= C ) ) -> ( # ` ( A \ { B , C } ) ) = ( ( # ` A ) - 2 ) )

  proof
    cA
    cfn
    wcel
    #
    cB
    cA
    wcel
    #
    cC
    cA
    wcel
    #
    cB
    cC
    wne
    #
    w3a
    #
    wa
    #
    cA
    cB
    cC
    cpr
    cdif
    #
    chash
    cfv
    cA
    cB
    csn
    #
    cdif
    #
    cC
    csn
    cdif
    #
    chash
    cfv
    #
    @8
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cA
    chash
    cfv
    #
    c2
    cmin
    co
    #
    @5
    @6
    @9
    chash
    @6
    @9
    wceq
    @5
    cA
    cB
    cC
    difpr
    a1i
    fveq2d
    @0
    @8
    cfn
    wcel
    @4
    cC
    @8
    wcel
    #
    @10
    @12
    wceq
    cA
    @7
    diffi
    @5
    @2
    cC
    cB
    wne
    #
    wa
    #
    @15
    @4
    @17
    @0
    @2
    @3
    @17
    @1
    @3
    @16
    @2
    @3
    @16
    cB
    cC
    necom
    biimpi
    anim2i
    3adant1
    adantl
    cC
    cA
    cB
    eldifsn
    sylibr
    @8
    cC
    hashdifsn
    syl2an2r
    @5
    @12
    @13
    c1
    cmin
    co
    #
    c1
    cmin
    co
    #
    @14
    @5
    @11
    @18
    c1
    cmin
    @0
    @2
    @1
    @11
    @18
    wceq
    @3
    cA
    cB
    hashdifsn
    3ad2antr1
    oveq1d
    @0
    @19
    @14
    wceq
    #
    @4
    @0
    @13
    cc
    wcel
    @20
    @0
    @13
    cA
    hashcl
    nn0cnd
    @13
    sub1m1
    syl
    adantr
    eqtrd
    3eqtrd
end
