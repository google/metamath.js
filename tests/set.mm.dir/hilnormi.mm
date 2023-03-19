include "chil.mm"
include "cv.mm"
include "cnmcv.mm"
include "cfv.mm"
include "cmpt.mm"
include "csp.mm"
include "co.mm"
include "csqrt.mm"
include "cno.mm"
include "cnv.mm"
include "wcel.mm"
include "wceq.mm"
include "eqid.mm"
include "ipnm.mm"
include "mpan.mm"
include "mpteq2ia.mm"
include "cr.mm"
include "nvf.mm"
include "feqmptd.mm"
include "ax-mp.mm"
include "dfhnorm2.mm"
include "3eqtr4ri.mm"

theorem hilnormi
  let cU: class U
  let vx: setvar x
  assume hilnorm.5: |- ~H = ( BaseSet ` U )
  assume hilnorm.2: |- .ih = ( .iOLD ` U )
  assume hilnorm.9: |- U e. NrmCVec


  assert |- normh = ( normCV ` U )

  proof
    vx
    chil
    vx
    cv
    #
    cU
    cnmcv
    cfv
    #
    cfv
    #
    cmpt
    #
    vx
    chil
    @0
    @0
    csp
    co
    csqrt
    cfv
    #
    cmpt
    @1
    cno
    vx
    chil
    @2
    @4
    cU
    cnv
    wcel
    #
    @0
    chil
    wcel
    @2
    @4
    wceq
    hilnorm.9
    @0
    csp
    cU
    @1
    chil
    hilnorm.5
    @1
    eqid
    #
    hilnorm.2
    ipnm
    mpan
    mpteq2ia
    @5
    @1
    @3
    wceq
    hilnorm.9
    @5
    vx
    chil
    cr
    @1
    cU
    @1
    chil
    hilnorm.5
    @6
    nvf
    feqmptd
    ax-mp
    vx
    dfhnorm2
    3eqtr4ri
end
