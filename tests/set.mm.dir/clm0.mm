include "cclm.mm"
include "wcel.mm"
include "cc0.mm"
include "ccnfld.mm"
include "cbs.mm"
include "cfv.mm"
include "cress.mm"
include "co.mm"
include "c0g.mm"
include "csubrg.mm"
include "wceq.mm"
include "eqid.mm"
include "clmsubrg.mm"
include "cnfld0.mm"
include "subrg0.mm"
include "syl.mm"
include "clmsca.mm"
include "fveq2d.mm"
include "eqtr4d.mm"

theorem clm0
  let cF: class F
  let cW: class W
  assume clm0.f: |- F = ( Scalar ` W )


  assert |- ( W e. CMod -> 0 = ( 0g ` F ) )

  proof
    cW
    cclm
    wcel
    #
    cc0
    ccnfld
    cF
    cbs
    cfv
    #
    cress
    co
    #
    c0g
    cfv
    #
    cF
    c0g
    cfv
    @0
    @1
    ccnfld
    csubrg
    cfv
    wcel
    cc0
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
    cc0
    @2
    eqid
    cnfld0
    subrg0
    syl
    @0
    cF
    @2
    c0g
    cF
    @1
    cW
    clm0.f
    @4
    clmsca
    fveq2d
    eqtr4d
end
