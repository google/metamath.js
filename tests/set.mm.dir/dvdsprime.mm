include "cprime.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "wceq.mm"
include "c1.mm"
include "wo.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "isprm2.mm"
include "breq1.mm"
include "eqeq1.mm"
include "orbi12d.mm"
include "orcom.mm"
include "syl6bb.mm"
include "imbi12d.mm"
include "rspccva.mm"
include "adantll.mm"
include "sylanb.mm"
include "cz.mm"
include "prmz.mm"
include "iddvds.mm"
include "syl.mm"
include "adantr.mm"
include "syl5ibrcom.mm"
include "1dvds.mm"
include "jaod.mm"
include "impbid.mm"

theorem dvdsprime
  let cP: class P
  let cM: class M
  let vm: setvar m


  assert |- ( ( P e. Prime /\ M e. NN ) -> ( M || P <-> ( M = P \/ M = 1 ) ) )

  proof
    cP
    cprime
    wcel
    #
    cM
    cn
    wcel
    #
    wa
    #
    cM
    cP
    cdvds
    wbr
    #
    cM
    cP
    wceq
    #
    cM
    c1
    wceq
    #
    wo
    #
    @0
    cP
    c2
    cuz
    cfv
    wcel
    #
    vm
    cv
    #
    cP
    cdvds
    wbr
    #
    @8
    c1
    wceq
    #
    @8
    cP
    wceq
    #
    wo
    #
    wi
    #
    vm
    cn
    wral
    #
    wa
    @1
    @3
    @6
    wi
    #
    vm
    cP
    isprm2
    @14
    @1
    @15
    @7
    @13
    @15
    vm
    cM
    cn
    @8
    cM
    wceq
    #
    @9
    @3
    @12
    @6
    @8
    cM
    cP
    cdvds
    breq1
    @16
    @12
    @5
    @4
    wo
    @6
    @16
    @10
    @5
    @11
    @4
    @8
    cM
    c1
    eqeq1
    @8
    cM
    cP
    eqeq1
    orbi12d
    @5
    @4
    orcom
    syl6bb
    imbi12d
    rspccva
    adantll
    sylanb
    @2
    @4
    @3
    @5
    @2
    @3
    @4
    cP
    cP
    cdvds
    wbr
    #
    @0
    @17
    @1
    @0
    cP
    cz
    wcel
    #
    @17
    cP
    prmz
    #
    cP
    iddvds
    syl
    adantr
    cM
    cP
    cP
    cdvds
    breq1
    syl5ibrcom
    @2
    @3
    @5
    c1
    cP
    cdvds
    wbr
    #
    @0
    @20
    @1
    @0
    @18
    @20
    @19
    cP
    1dvds
    syl
    adantr
    cM
    c1
    cP
    cdvds
    breq1
    syl5ibrcom
    jaod
    impbid
end
