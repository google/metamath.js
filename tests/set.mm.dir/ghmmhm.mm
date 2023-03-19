include "cghm.mm"
include "co.mm"
include "wcel.mm"
include "cmnd.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "cplusg.mm"
include "wceq.mm"
include "wral.mm"
include "c0g.mm"
include "w3a.mm"
include "cmhm.mm"
include "cgrp.mm"
include "ghmgrp1.mm"
include "grpmnd.mm"
include "syl.mm"
include "ghmgrp2.mm"
include "jca.mm"
include "eqid.mm"
include "ghmf.mm"
include "ghmlin.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "ghmid.mm"
include "3jca.mm"
include "ismhm.mm"
include "sylanbrc.mm"

theorem ghmmhm
  let cS: class S
  let cT: class T
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f


  assert |- ( F e. ( S GrpHom T ) -> F e. ( S MndHom T ) )

  proof
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    cS
    cmnd
    wcel
    #
    cT
    cmnd
    wcel
    #
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
    #
    vx
    cv
    #
    vy
    cv
    #
    cS
    cplusg
    cfv
    #
    co
    cF
    cfv
    @6
    cF
    cfv
    @7
    cF
    cfv
    cT
    cplusg
    cfv
    #
    co
    wceq
    #
    vy
    @3
    wral
    vx
    @3
    wral
    #
    cS
    c0g
    cfv
    #
    cF
    cfv
    cT
    c0g
    cfv
    #
    wceq
    #
    w3a
    cF
    cS
    cT
    cmhm
    co
    wcel
    @0
    @1
    @2
    @0
    cS
    cgrp
    wcel
    @1
    cS
    cT
    cF
    ghmgrp1
    cS
    grpmnd
    syl
    @0
    cT
    cgrp
    wcel
    @2
    cS
    cT
    cF
    ghmgrp2
    cT
    grpmnd
    syl
    jca
    @0
    @5
    @11
    @14
    cS
    cT
    cF
    @3
    @4
    @3
    eqid
    #
    @4
    eqid
    #
    ghmf
    @0
    @10
    vx
    vy
    @3
    @3
    @0
    @6
    @3
    wcel
    @7
    @3
    wcel
    @10
    @8
    @9
    cS
    cT
    @6
    cF
    @7
    @3
    @15
    @8
    eqid
    #
    @9
    eqid
    #
    ghmlin
    3expb
    ralrimivva
    cS
    cT
    cF
    @12
    @13
    @12
    eqid
    #
    @13
    eqid
    #
    ghmid
    3jca
    vx
    vy
    @3
    @4
    @8
    @9
    cS
    cT
    cF
    @13
    @12
    @15
    @16
    @17
    @18
    @19
    @20
    ismhm
    sylanbrc
end
