include "cprime.mm"
include "wcel.mm"
include "cn.mm"
include "cn0.mm"
include "w3a.mm"
include "cexp.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "cpc.mm"
include "simp1.mm"
include "simp2.mm"
include "pccld.mm"
include "adantr.mm"
include "wb.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "adantl.mm"
include "simpl3.mm"
include "breq2d.mm"
include "simpr.mm"
include "rspcedvd.mm"
include "pcprmpw2.mm"
include "3adant3.mm"
include "mpbid.mm"
include "ex.mm"

theorem dvdsprmpweq
  let cA: class A
  let cP: class P
  let vn: setvar n
  let cN: class N

  disjoint A n
  disjoint N n
  disjoint P n
  assert |- ( ( P e. Prime /\ A e. NN /\ N e. NN0 ) -> ( A || ( P ^ N ) -> E. n e. NN0 A = ( P ^ n ) ) )

  proof
    cP
    cprime
    wcel
    #
    cA
    cn
    wcel
    #
    cN
    cn0
    wcel
    #
    w3a
    #
    cA
    cP
    cN
    cexp
    co
    #
    cdvds
    wbr
    #
    cA
    cP
    vn
    cv
    #
    cexp
    co
    #
    wceq
    #
    vn
    cn0
    wrex
    @3
    @5
    wa
    #
    @8
    cA
    cP
    cP
    cA
    cpc
    co
    #
    cexp
    co
    #
    wceq
    #
    vn
    @10
    cn0
    @3
    @10
    cn0
    wcel
    @5
    @3
    cP
    cA
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    pccld
    adantr
    @6
    @10
    wceq
    #
    @8
    @12
    wb
    @9
    @13
    @7
    @11
    cA
    @6
    @10
    cP
    cexp
    oveq2
    eqeq2d
    adantl
    @9
    cA
    @7
    cdvds
    wbr
    #
    vn
    cn0
    wrex
    #
    @12
    @9
    @14
    @5
    vn
    cN
    cn0
    @0
    @1
    @2
    @5
    simpl3
    @6
    cN
    wceq
    #
    @14
    @5
    wb
    @9
    @16
    @7
    @4
    cA
    cdvds
    @6
    cN
    cP
    cexp
    oveq2
    breq2d
    adantl
    @3
    @5
    simpr
    rspcedvd
    @3
    @15
    @12
    wb
    #
    @5
    @0
    @1
    @17
    @2
    cA
    cP
    vn
    pcprmpw2
    3adant3
    adantr
    mpbid
    rspcedvd
    ex
end
