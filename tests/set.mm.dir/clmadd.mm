include "cclm.mm"
include "wcel.mm"
include "cplusg.mm"
include "cfv.mm"
include "ccnfld.mm"
include "cbs.mm"
include "cress.mm"
include "co.mm"
include "caddc.mm"
include "eqid.mm"
include "clmsca.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wceq.mm"
include "fvex.mm"
include "cnfldadd.mm"
include "ressplusg.mm"
include "ax-mp.mm"
include "syl6reqr.mm"

theorem clmadd
  let cF: class F
  let cW: class W
  assume clm0.f: |- F = ( Scalar ` W )


  assert |- ( W e. CMod -> + = ( +g ` F ) )

  proof
    cW
    cclm
    wcel
    #
    cF
    cplusg
    cfv
    ccnfld
    cF
    cbs
    cfv
    #
    cress
    co
    #
    cplusg
    cfv
    #
    caddc
    @0
    cF
    @2
    cplusg
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
    caddc
    @3
    wceq
    cF
    cbs
    fvex
    @1
    caddc
    ccnfld
    @2
    cvv
    @2
    eqid
    cnfldadd
    ressplusg
    ax-mp
    syl6reqr
end
