include "cclm.mm"
include "wcel.mm"
include "c1.mm"
include "ccnfld.mm"
include "cbs.mm"
include "cfv.mm"
include "cress.mm"
include "co.mm"
include "cur.mm"
include "csubrg.mm"
include "wceq.mm"
include "eqid.mm"
include "clmsubrg.mm"
include "cnfld1.mm"
include "subrg1.mm"
include "syl.mm"
include "clmsca.mm"
include "fveq2d.mm"
include "eqtr4d.mm"

theorem clm1
  let cF: class F
  let cW: class W
  assume clm0.f: |- F = ( Scalar ` W )


  assert |- ( W e. CMod -> 1 = ( 1r ` F ) )

  proof
    cW
    cclm
    wcel
    #
    c1
    ccnfld
    cF
    cbs
    cfv
    #
    cress
    co
    #
    cur
    cfv
    #
    cF
    cur
    cfv
    @0
    @1
    ccnfld
    csubrg
    cfv
    wcel
    c1
    @3
    wceq
    cF
    @1
    cW
    clm0.f
    @1
    eqid
    #
    clmsubrg
    @1
    ccnfld
    @2
    c1
    @2
    eqid
    cnfld1
    subrg1
    syl
    @0
    cF
    @2
    cur
    cF
    @1
    cW
    clm0.f
    @4
    clmsca
    fveq2d
    eqtr4d
end
