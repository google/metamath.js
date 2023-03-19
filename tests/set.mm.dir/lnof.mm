include "cnv.mm"
include "wcel.mm"
include "wf.mm"
include "wa.mm"
include "cv.mm"
include "cns.mm"
include "cfv.mm"
include "co.mm"
include "cpv.mm"
include "wceq.mm"
include "wral.mm"
include "cc.mm"
include "eqid.mm"
include "islno.mm"
include "simprbda.mm"
include "3impa.mm"

theorem lnof
  let cT: class T
  let cU: class U
  let cL: class L
  let cW: class W
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume lnof.1: |- X = ( BaseSet ` U )
  assume lnof.2: |- Y = ( BaseSet ` W )
  assume lnof.7: |- L = ( U LnOp W )


  assert |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. L ) -> T : X --> Y )

  proof
    cU
    cnv
    wcel
    #
    cW
    cnv
    wcel
    #
    cT
    cL
    wcel
    #
    cX
    cY
    cT
    wf
    #
    @0
    @1
    wa
    @2
    @3
    vx
    cv
    #
    vy
    cv
    #
    cU
    cns
    cfv
    #
    co
    vz
    cv
    #
    cU
    cpv
    cfv
    #
    co
    cT
    cfv
    @4
    @5
    cT
    cfv
    cW
    cns
    cfv
    #
    co
    @7
    cT
    cfv
    cW
    cpv
    cfv
    #
    co
    wceq
    vz
    cX
    wral
    vy
    cX
    wral
    vx
    cc
    wral
    vx
    vy
    vz
    @6
    @9
    cT
    cU
    @8
    @10
    cL
    cW
    cX
    cY
    lnof.1
    lnof.2
    @8
    eqid
    @10
    eqid
    @6
    eqid
    @9
    eqid
    lnof.7
    islno
    simprbda
    3impa
end
