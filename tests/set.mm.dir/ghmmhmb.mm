include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "cghm.mm"
include "co.mm"
include "cmhm.mm"
include "cv.mm"
include "ghmmhm.mm"
include "cplusg.mm"
include "cfv.mm"
include "cbs.mm"
include "eqid.mm"
include "simpll.mm"
include "simplr.mm"
include "wf.mm"
include "mhmf.mm"
include "adantl.mm"
include "wceq.mm"
include "mhmlin.mm"
include "3expb.mm"
include "adantll.mm"
include "isghmd.mm"
include "ex.mm"
include "impbid2.mm"
include "eqrdv.mm"

theorem ghmmhmb
  let cS: class S
  let cT: class T
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f


  assert |- ( ( S e. Grp /\ T e. Grp ) -> ( S GrpHom T ) = ( S MndHom T ) )

  proof
    cS
    cgrp
    wcel
    #
    cT
    cgrp
    wcel
    #
    wa
    #
    vf
    cS
    cT
    cghm
    co
    #
    cS
    cT
    cmhm
    co
    #
    @2
    vf
    cv
    #
    @3
    wcel
    #
    @5
    @4
    wcel
    #
    cS
    cT
    @5
    ghmmhm
    @2
    @7
    @6
    @2
    @7
    wa
    vx
    vy
    cS
    cplusg
    cfv
    #
    cT
    cplusg
    cfv
    #
    cS
    cT
    @5
    cS
    cbs
    cfv
    #
    cT
    cbs
    cfv
    #
    @10
    eqid
    #
    @11
    eqid
    #
    @8
    eqid
    #
    @9
    eqid
    #
    @0
    @1
    @7
    simpll
    @0
    @1
    @7
    simplr
    @7
    @10
    @11
    @5
    wf
    @2
    @10
    @11
    cS
    cT
    @5
    @12
    @13
    mhmf
    adantl
    @7
    vx
    cv
    #
    @10
    wcel
    #
    vy
    cv
    #
    @10
    wcel
    #
    wa
    @16
    @18
    @8
    co
    @5
    cfv
    @16
    @5
    cfv
    @18
    @5
    cfv
    @9
    co
    wceq
    #
    @2
    @7
    @17
    @19
    @20
    @10
    @8
    @9
    cS
    cT
    @5
    @16
    @18
    @12
    @14
    @15
    mhmlin
    3expb
    adantll
    isghmd
    ex
    impbid2
    eqrdv
end
