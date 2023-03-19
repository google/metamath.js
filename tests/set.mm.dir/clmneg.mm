include "cclm.mm"
include "wcel.mm"
include "wa.mm"
include "cminusg.mm"
include "cfv.mm"
include "ccnfld.mm"
include "cress.mm"
include "co.mm"
include "cneg.mm"
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
include "subginv.mm"
include "sylan.mm"
include "cc.mm"
include "clmsscn.mm"
include "sselda.mm"
include "cnfldneg.mm"
include "3eqtr2rd.mm"

theorem clmneg
  let cA: class A
  let cF: class F
  let cK: class K
  let cW: class W
  assume clm0.f: |- F = ( Scalar ` W )
  assume clmsub.k: |- K = ( Base ` F )


  assert |- ( ( W e. CMod /\ A e. K ) -> -u A = ( ( invg ` F ) ` A ) )

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
    cminusg
    cfv
    #
    cfv
    cA
    ccnfld
    cK
    cress
    co
    #
    cminusg
    cfv
    #
    cfv
    #
    cA
    ccnfld
    cminusg
    cfv
    #
    cfv
    #
    cA
    cneg
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
    cminusg
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
    @8
    @6
    wceq
    @0
    cK
    ccnfld
    csubrg
    cfv
    wcel
    @10
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
    @7
    @5
    cA
    @4
    eqid
    @7
    eqid
    @5
    eqid
    subginv
    sylan
    @2
    cA
    cc
    wcel
    @8
    @9
    wceq
    @0
    cK
    cc
    cA
    cF
    cK
    cW
    clm0.f
    clmsub.k
    clmsscn
    sselda
    cA
    cnfldneg
    syl
    3eqtr2rd
end
