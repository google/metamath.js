include "cnv.mm"
include "wcel.mm"
include "cpv.mm"
include "cfv.mm"
include "cns.mm"
include "cop.mm"
include "cvc.mm"
include "cr.mm"
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
include "eqid.mm"
include "nvi.mm"
include "simp2d.mm"

theorem nvf
  let cU: class U
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume nvf.1: |- X = ( BaseSet ` U )
  assume nvf.6: |- N = ( normCV ` U )


  assert |- ( U e. NrmCVec -> N : X --> RR )

  proof
    cU
    cnv
    wcel
    cU
    cpv
    cfv
    #
    cU
    cns
    cfv
    #
    cop
    cvc
    wcel
    cX
    cr
    cN
    wf
    vx
    cv
    #
    cN
    cfv
    #
    cc0
    wceq
    @2
    cU
    cn0v
    cfv
    #
    wceq
    wi
    vy
    cv
    #
    @2
    @1
    co
    cN
    cfv
    @5
    cabs
    cfv
    @3
    cmul
    co
    wceq
    vy
    cc
    wral
    @2
    @5
    @0
    co
    cN
    cfv
    @3
    @5
    cN
    cfv
    caddc
    co
    cle
    wbr
    vy
    cX
    wral
    w3a
    vx
    cX
    wral
    vx
    vy
    @1
    cU
    @0
    cN
    cX
    @4
    nvf.1
    @0
    eqid
    @1
    eqid
    @4
    eqid
    nvf.6
    nvi
    simp2d
end
