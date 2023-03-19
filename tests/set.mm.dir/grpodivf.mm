include "cgr.mm"
include "wcel.mm"
include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "cgn.mm"
include "cfv.mm"
include "co.mm"
include "cmpt2.mm"
include "wral.mm"
include "eqid.mm"
include "grpoinvcl.mm"
include "3adant2.mm"
include "grpocl.mm"
include "syld3an3.mm"
include "3expib.mm"
include "ralrimivv.mm"
include "fmpt2.mm"
include "sylib.mm"
include "grpodivfval.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem grpodivf
  let cD: class D
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume grpdivf.1: |- X = ran G
  assume grpdivf.3: |- D = ( /g ` G )


  assert |- ( G e. GrpOp -> D : ( X X. X ) --> X )

  proof
    cG
    cgr
    wcel
    #
    cX
    cX
    cxp
    #
    cX
    cD
    wf
    @1
    cX
    vx
    vy
    cX
    cX
    vx
    cv
    #
    vy
    cv
    #
    cG
    cgn
    cfv
    #
    cfv
    #
    cG
    co
    #
    cmpt2
    #
    wf
    #
    @0
    @6
    cX
    wcel
    #
    vy
    cX
    wral
    vx
    cX
    wral
    @8
    @0
    @9
    vx
    vy
    cX
    cX
    @0
    @2
    cX
    wcel
    #
    @3
    cX
    wcel
    #
    @9
    @0
    @10
    @11
    @5
    cX
    wcel
    #
    @9
    @0
    @11
    @12
    @10
    @3
    cG
    @4
    cX
    grpdivf.1
    @4
    eqid
    #
    grpoinvcl
    3adant2
    @2
    @5
    cG
    cX
    grpdivf.1
    grpocl
    syld3an3
    3expib
    ralrimivv
    vx
    vy
    cX
    cX
    @6
    cX
    @7
    @7
    eqid
    fmpt2
    sylib
    @0
    @1
    cX
    cD
    @7
    vx
    vy
    cD
    cG
    @4
    cX
    grpdivf.1
    @13
    grpdivf.3
    grpodivfval
    feq1d
    mpbird
end
