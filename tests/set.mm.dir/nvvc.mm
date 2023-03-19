include "cnv.mm"
include "wcel.mm"
include "cpv.mm"
include "cfv.mm"
include "cns.mm"
include "cop.mm"
include "cvc.mm"
include "eqid.mm"
include "nvvop.mm"
include "cba.mm"
include "cr.mm"
include "cnmcv.mm"
include "wf.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "cn0v.mm"
include "wi.mm"
include "co.mm"
include "cabs.mm"
include "cmul.mm"
include "cc.mm"
include "wral.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "nvi.mm"
include "simp1d.mm"
include "eqeltrd.mm"

theorem nvvc
  let cU: class U
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume nvvc.1: |- W = ( 1st ` U )


  assert |- ( U e. NrmCVec -> W e. CVecOLD )

  proof
    cU
    cnv
    wcel
    #
    cW
    cU
    cpv
    cfv
    #
    cU
    cns
    cfv
    #
    cop
    #
    cvc
    @2
    cU
    @1
    cW
    nvvc.1
    @1
    eqid
    #
    @2
    eqid
    #
    nvvop
    @0
    @3
    cvc
    wcel
    cU
    cba
    cfv
    #
    cr
    cU
    cnmcv
    cfv
    #
    wf
    vx
    cv
    #
    @7
    cfv
    #
    cc0
    wceq
    @8
    cU
    cn0v
    cfv
    #
    wceq
    wi
    vy
    cv
    #
    @8
    @2
    co
    @7
    cfv
    @11
    cabs
    cfv
    @9
    cmul
    co
    wceq
    vy
    cc
    wral
    @8
    @11
    @1
    co
    @7
    cfv
    @9
    @11
    @7
    cfv
    caddc
    co
    cle
    wbr
    vy
    @6
    wral
    w3a
    vx
    @6
    wral
    vx
    vy
    @2
    cU
    @1
    @7
    @6
    @10
    @6
    eqid
    @4
    @5
    @10
    eqid
    @7
    eqid
    nvi
    simp1d
    eqeltrd
end
