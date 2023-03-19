include "cclm.mm"
include "wcel.mm"
include "cstv.mm"
include "cfv.mm"
include "ccnfld.mm"
include "cbs.mm"
include "cress.mm"
include "co.mm"
include "ccj.mm"
include "eqid.mm"
include "clmsca.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wceq.mm"
include "fvex.mm"
include "cnfldcj.mm"
include "ressstarv.mm"
include "ax-mp.mm"
include "syl6reqr.mm"

theorem clmcj
  let cF: class F
  let cW: class W
  assume clm0.f: |- F = ( Scalar ` W )


  assert |- ( W e. CMod -> * = ( *r ` F ) )

  proof
    cW
    cclm
    wcel
    #
    cF
    cstv
    cfv
    ccnfld
    cF
    cbs
    cfv
    #
    cress
    co
    #
    cstv
    cfv
    #
    ccj
    @0
    cF
    @2
    cstv
    cF
    @1
    cW
    clm0.f
    @1
    eqid
    clmsca
    fveq2d
    @1
    cvv
    wcel
    ccj
    @3
    wceq
    cF
    cbs
    fvex
    @1
    ccnfld
    @2
    ccj
    cvv
    @2
    eqid
    cnfldcj
    ressstarv
    ax-mp
    syl6reqr
end
