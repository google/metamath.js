include "cprime.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cn0.mm"
include "wrex.mm"
include "cpc.mm"
include "cdvds.mm"
include "wbr.mm"
include "cz.mm"
include "prmz.mm"
include "adantr.mm"
include "zexpcl.mm"
include "sylan.mm"
include "iddvds.mm"
include "syl.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "reximdva.mm"
include "pcprmpw2.mm"
include "sylibd.mm"
include "wi.mm"
include "pccl.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "ex.mm"
include "impbid.mm"

theorem pcprmpw
  let cA: class A
  let cP: class P
  let vn: setvar n
  let vp: setvar p

  disjoint A n
  disjoint P n
  disjoint n p
  disjoint A p
  disjoint P p
  assert |- ( ( P e. Prime /\ A e. NN ) -> ( E. n e. NN0 A = ( P ^ n ) <-> A = ( P ^ ( P pCnt A ) ) ) )

  proof
    cP
    cprime
    wcel
    #
    cA
    cn
    wcel
    #
    wa
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
    #
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
    @2
    @6
    cA
    @4
    cdvds
    wbr
    #
    vn
    cn0
    wrex
    @9
    @2
    @5
    @10
    vn
    cn0
    @2
    @3
    cn0
    wcel
    #
    wa
    #
    @10
    @5
    @4
    @4
    cdvds
    wbr
    #
    @12
    @4
    cz
    wcel
    #
    @13
    @2
    cP
    cz
    wcel
    #
    @11
    @14
    @0
    @15
    @1
    cP
    prmz
    adantr
    cP
    @3
    zexpcl
    sylan
    @4
    iddvds
    syl
    cA
    @4
    @4
    cdvds
    breq1
    syl5ibrcom
    reximdva
    cA
    cP
    vn
    pcprmpw2
    sylibd
    @2
    @7
    cn0
    wcel
    #
    @9
    @6
    wi
    cP
    cA
    pccl
    @16
    @9
    @6
    @5
    @9
    vn
    @7
    cn0
    @3
    @7
    wceq
    @4
    @8
    cA
    @3
    @7
    cP
    cexp
    oveq2
    eqeq2d
    rspcev
    ex
    syl
    impbid
end
