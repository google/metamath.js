include "cghm.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "cgrp.mm"
include "wa.mm"
include "eqid.mm"
include "isghm.mm"
include "simprbi.mm"
include "simpld.mm"

theorem ghmf
  let cS: class S
  let cT: class T
  let cF: class F
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume ghmf.x: |- X = ( Base ` S )
  assume ghmf.y: |- Y = ( Base ` T )


  assert |- ( F e. ( S GrpHom T ) -> F : X --> Y )

  proof
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    cX
    cY
    cF
    wf
    #
    vy
    cv
    #
    vx
    cv
    #
    cS
    cplusg
    cfv
    #
    co
    cF
    cfv
    @2
    cF
    cfv
    @3
    cF
    cfv
    cT
    cplusg
    cfv
    #
    co
    wceq
    vx
    cX
    wral
    vy
    cX
    wral
    #
    @0
    cS
    cgrp
    wcel
    cT
    cgrp
    wcel
    wa
    @1
    @6
    wa
    vx
    vy
    @4
    @5
    cS
    cT
    cF
    cX
    cY
    ghmf.x
    ghmf.y
    @4
    eqid
    @5
    eqid
    isghm
    simprbi
    simpld
end
