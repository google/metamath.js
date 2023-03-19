include "cclm.mm"
include "wcel.mm"
include "wa.mm"
include "cnm.mm"
include "cfv.mm"
include "ccnfld.mm"
include "cress.mm"
include "co.mm"
include "cabs.mm"
include "wceq.mm"
include "clmsca.mm"
include "fveq2d.mm"
include "adantr.mm"
include "fveq1d.mm"
include "csubg.mm"
include "csubrg.mm"
include "clmsubrg.mm"
include "subrgsubg.mm"
include "syl.mm"
include "eqid.mm"
include "cnfldnm.mm"
include "subgnm2.mm"
include "sylan.mm"
include "eqtr2d.mm"

theorem clmabs
  let cA: class A
  let cF: class F
  let cK: class K
  let cW: class W
  assume clm0.f: |- F = ( Scalar ` W )
  assume clmsub.k: |- K = ( Base ` F )


  assert |- ( ( W e. CMod /\ A e. K ) -> ( abs ` A ) = ( ( norm ` F ) ` A ) )

  proof
    cW
    cclm
    wcel
    #
    cA
    cK
    wcel
    #
    wa
    #
    cA
    cF
    cnm
    cfv
    #
    cfv
    cA
    ccnfld
    cK
    cress
    co
    #
    cnm
    cfv
    #
    cfv
    #
    cA
    cabs
    cfv
    #
    @2
    cA
    @3
    @5
    @0
    @3
    @5
    wceq
    @1
    @0
    cF
    @4
    cnm
    cF
    cK
    cW
    clm0.f
    clmsub.k
    clmsca
    fveq2d
    adantr
    fveq1d
    @0
    cK
    ccnfld
    csubg
    cfv
    wcel
    #
    @1
    @6
    @7
    wceq
    @0
    cK
    ccnfld
    csubrg
    cfv
    wcel
    @8
    cF
    cK
    cW
    clm0.f
    clmsub.k
    clmsubrg
    cK
    ccnfld
    subrgsubg
    syl
    cK
    ccnfld
    @4
    @5
    cabs
    cA
    @4
    eqid
    cnfldnm
    @5
    eqid
    subgnm2
    sylan
    eqtr2d
end
