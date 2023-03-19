include "cghm.mm"
include "co.mm"
include "wcel.mm"
include "cgrp.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "cplusg.mm"
include "wceq.mm"
include "wral.mm"
include "eqid.mm"
include "isghm.mm"
include "simplbi.mm"
include "simprd.mm"

theorem ghmgrp2
  let cS: class S
  let cT: class T
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  let cY: class Y


  assert |- ( F e. ( S GrpHom T ) -> T e. Grp )

  proof
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    cS
    cgrp
    wcel
    #
    cT
    cgrp
    wcel
    #
    @0
    @1
    @2
    wa
    cS
    cbs
    cfv
    #
    cT
    cbs
    cfv
    #
    cF
    wf
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
    @5
    cF
    cfv
    @6
    cF
    cfv
    cT
    cplusg
    cfv
    #
    co
    wceq
    vx
    @3
    wral
    vy
    @3
    wral
    wa
    vx
    vy
    @7
    @8
    cS
    cT
    cF
    @3
    @4
    @3
    eqid
    @4
    eqid
    @7
    eqid
    @8
    eqid
    isghm
    simplbi
    simprd
end
