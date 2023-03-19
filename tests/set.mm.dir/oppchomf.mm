include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "chom.mm"
include "co.mm"
include "cmpt2.mm"
include "chomf.mm"
include "ctpos.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "eqid.mm"
include "oppchom.mm"
include "a1i.mm"
include "mpt2eq3ia.mm"
include "oppcbas.mm"
include "homffval.mm"
include "tposmpt2.mm"
include "3eqtr4ri.mm"

theorem oppchomf
  let cC: class C
  let cH: class H
  let cO: class O
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume oppcbas.1: |- O = ( oppCat ` C )
  assume oppchomf.h: |- H = ( Homf ` C )


  assert |- tpos H = ( Homf ` O )

  proof
    vy
    vx
    cC
    cbs
    cfv
    #
    @0
    vy
    cv
    #
    vx
    cv
    #
    cO
    chom
    cfv
    #
    co
    #
    cmpt2
    vy
    vx
    @0
    @0
    @2
    @1
    cC
    chom
    cfv
    #
    co
    #
    cmpt2
    cO
    chomf
    cfv
    #
    cH
    ctpos
    vy
    vx
    @0
    @0
    @4
    @6
    @4
    @6
    wceq
    @1
    @0
    wcel
    @2
    @0
    wcel
    wa
    cC
    @5
    cO
    @1
    @2
    @5
    eqid
    #
    oppcbas.1
    oppchom
    a1i
    mpt2eq3ia
    vy
    vx
    @0
    cO
    @7
    @3
    @7
    eqid
    @0
    cC
    cO
    oppcbas.1
    @0
    eqid
    #
    oppcbas
    @3
    eqid
    homffval
    vx
    vy
    @0
    @0
    @6
    cH
    vx
    vy
    @0
    cC
    cH
    @5
    oppchomf.h
    @9
    @8
    homffval
    tposmpt2
    3eqtr4ri
end
