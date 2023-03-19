include "crg.mm"
include "wcel.mm"
include "cui.mm"
include "cfv.mm"
include "cbs.mm"
include "c0g.mm"
include "csn.mm"
include "cdif.mm"
include "wceq.mm"
include "wa.mm"
include "cdr.mm"
include "eqidd.mm"
include "a1i.mm"
include "cv.mm"
include "cmulr.mm"
include "co.mm"
include "oveqi.mm"
include "unitpropd.mm"
include "cplusg.mm"
include "grpidpropd.mm"
include "sneqd.mm"
include "difeq2d.mm"
include "eqeq12d.mm"
include "pm5.32i.mm"
include "ringprop.mm"
include "anbi1i.mm"
include "bitri.mm"
include "eqid.mm"
include "isdrng.mm"
include "3bitr4i.mm"

theorem drngprop
  let cK: class K
  let cL: class L
  let vx: setvar x
  let vy: setvar y
  assume drngprop.b: |- ( Base ` K ) = ( Base ` L )
  assume drngprop.p: |- ( +g ` K ) = ( +g ` L )
  assume drngprop.m: |- ( .r ` K ) = ( .r ` L )


  assert |- ( K e. DivRing <-> L e. DivRing )

  proof
    cK
    crg
    wcel
    #
    cK
    cui
    cfv
    #
    cK
    cbs
    cfv
    #
    cK
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    wceq
    #
    wa
    #
    cL
    crg
    wcel
    #
    cL
    cui
    cfv
    #
    @2
    cL
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    wceq
    #
    wa
    #
    cK
    cdr
    wcel
    cL
    cdr
    wcel
    @7
    @0
    @13
    wa
    @14
    @0
    @6
    @13
    @0
    @1
    @9
    @5
    @12
    @0
    vx
    vy
    @2
    cK
    cL
    @0
    @2
    eqidd
    #
    @2
    cL
    cbs
    cfv
    wceq
    @0
    drngprop.b
    a1i
    #
    vx
    cv
    #
    vy
    cv
    #
    cK
    cmulr
    cfv
    #
    co
    @17
    @18
    cL
    cmulr
    cfv
    #
    co
    wceq
    @0
    @17
    @2
    wcel
    @18
    @2
    wcel
    wa
    wa
    #
    @19
    @20
    @17
    @18
    drngprop.m
    oveqi
    a1i
    unitpropd
    @0
    @4
    @11
    @2
    @0
    @3
    @10
    @0
    vx
    vy
    @2
    cK
    cL
    @15
    @16
    @17
    @18
    cK
    cplusg
    cfv
    #
    co
    @17
    @18
    cL
    cplusg
    cfv
    #
    co
    wceq
    @21
    @22
    @23
    @17
    @18
    drngprop.p
    oveqi
    a1i
    grpidpropd
    sneqd
    difeq2d
    eqeq12d
    pm5.32i
    @0
    @8
    @13
    cK
    cL
    drngprop.b
    drngprop.p
    drngprop.m
    ringprop
    anbi1i
    bitri
    @2
    cK
    @1
    @3
    @2
    eqid
    @1
    eqid
    @3
    eqid
    isdrng
    @2
    cL
    @9
    @10
    drngprop.b
    @9
    eqid
    @10
    eqid
    isdrng
    3bitr4i
end
