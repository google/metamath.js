include "cga.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wral.mm"
include "cplusg.mm"
include "cfv.mm"
include "cbs.mm"
include "wa.mm"
include "cxp.mm"
include "wf.mm"
include "cgrp.mm"
include "cvv.mm"
include "eqid.mm"
include "isga.mm"
include "simprbi.mm"
include "simprd.mm"
include "simpl.mm"
include "ralimi.mm"
include "syl.mm"
include "oveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "rspccva.mm"
include "sylan.mm"

theorem gagrpid
  let cA: class A
  let c.po: class .(+)
  let cG: class G
  let cY: class Y
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume gagrpid.1: |- .0. = ( 0g ` G )


  assert |- ( ( .(+) e. ( G GrpAct Y ) /\ A e. Y ) -> ( .0. .(+) A ) = A )

  proof
    c.po
    cG
    cY
    cga
    co
    wcel
    #
    c.0
    vx
    cv
    #
    c.po
    co
    #
    @1
    wceq
    #
    vx
    cY
    wral
    #
    cA
    cY
    wcel
    c.0
    cA
    c.po
    co
    #
    cA
    wceq
    #
    @0
    @3
    vy
    cv
    #
    vz
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    @1
    c.po
    co
    @7
    @8
    @1
    c.po
    co
    c.po
    co
    wceq
    vz
    cG
    cbs
    cfv
    #
    wral
    vy
    @10
    wral
    #
    wa
    #
    vx
    cY
    wral
    #
    @4
    @0
    @10
    cY
    cxp
    cY
    c.po
    wf
    #
    @13
    @0
    cG
    cgrp
    wcel
    cY
    cvv
    wcel
    wa
    @14
    @13
    wa
    vx
    vy
    vz
    @9
    c.po
    cG
    @10
    cY
    c.0
    @10
    eqid
    @9
    eqid
    gagrpid.1
    isga
    simprbi
    simprd
    @12
    @3
    vx
    cY
    @3
    @11
    simpl
    ralimi
    syl
    @3
    @6
    vx
    cA
    cY
    @1
    cA
    wceq
    #
    @2
    @5
    @1
    cA
    @1
    cA
    c.0
    c.po
    oveq2
    @15
    id
    eqeq12d
    rspccva
    sylan
end
