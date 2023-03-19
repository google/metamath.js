include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cghm.mm"
include "co.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmhm.mm"
include "crh.mm"
include "simpl.mm"
include "pwsring.mm"
include "jca.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "pwsdiagghm.mm"
include "sylan.mm"
include "cpws.mm"
include "cmnd.mm"
include "eqid.mm"
include "ringmgp.mm"
include "mgpbas.mm"
include "pwsdiagmhm.mm"
include "cbs.mm"
include "eqidd.mm"
include "wceq.mm"
include "cplusg.mm"
include "pwsmgp.mm"
include "simpld.mm"
include "cv.mm"
include "simprd.mm"
include "oveqdr.mm"
include "mhmpropd.mm"
include "eleqtrrd.mm"
include "isrhm.mm"
include "sylanbrc.mm"

theorem pwsdiagrhm
  let vx: setvar x
  let cB: class B
  let cR: class R
  let cF: class F
  let cI: class I
  let cW: class W
  let cY: class Y
  let vy: setvar y
  let vz: setvar z
  assume pwsdiagrhm.y: |- Y = ( R ^s I )
  assume pwsdiagrhm.b: |- B = ( Base ` R )
  assume pwsdiagrhm.f: |- F = ( x e. B |-> ( I X. { x } ) )

  disjoint B x
  disjoint I x
  disjoint R x
  disjoint W x
  disjoint Y x
  disjoint F y
  disjoint F z
  disjoint y z
  disjoint I y
  disjoint I z
  disjoint R y
  disjoint R z
  disjoint W y
  disjoint W z
  disjoint Y y
  disjoint Y z
  assert |- ( ( R e. Ring /\ I e. W ) -> F e. ( R RingHom Y ) )

  proof
    cR
    crg
    wcel
    #
    cI
    cW
    wcel
    #
    wa
    #
    @0
    cY
    crg
    wcel
    #
    wa
    cF
    cR
    cY
    cghm
    co
    wcel
    #
    cF
    cR
    cmgp
    cfv
    #
    cY
    cmgp
    cfv
    #
    cmhm
    co
    #
    wcel
    #
    wa
    cF
    cR
    cY
    crh
    co
    wcel
    @2
    @0
    @3
    @0
    @1
    simpl
    cR
    cI
    cW
    cY
    pwsdiagrhm.y
    pwsring
    jca
    @2
    @4
    @8
    @0
    cR
    cgrp
    wcel
    @1
    @4
    cR
    ringgrp
    vx
    cB
    cR
    cF
    cI
    cW
    cY
    pwsdiagrhm.y
    pwsdiagrhm.b
    pwsdiagrhm.f
    pwsdiagghm
    sylan
    @2
    cF
    @5
    @5
    cI
    cpws
    co
    #
    cmhm
    co
    #
    @7
    @0
    @5
    cmnd
    wcel
    @1
    cF
    @10
    wcel
    cR
    @5
    @5
    eqid
    #
    ringmgp
    vx
    cB
    @5
    cF
    cI
    cW
    @9
    @9
    eqid
    #
    cB
    cR
    @5
    @11
    pwsdiagrhm.b
    mgpbas
    pwsdiagrhm.f
    pwsdiagmhm
    sylan
    @2
    vy
    vz
    @5
    cbs
    cfv
    #
    @6
    cbs
    cfv
    #
    @5
    @6
    @5
    @9
    @2
    @13
    eqidd
    #
    @2
    @14
    eqidd
    @15
    @2
    @14
    @9
    cbs
    cfv
    #
    wceq
    #
    @6
    cplusg
    cfv
    #
    @9
    cplusg
    cfv
    #
    wceq
    #
    @14
    @16
    @18
    @19
    cR
    cI
    @5
    @6
    crg
    cW
    cY
    @9
    pwsdiagrhm.y
    @11
    @12
    @6
    eqid
    #
    @14
    eqid
    @16
    eqid
    @18
    eqid
    @19
    eqid
    pwsmgp
    #
    simpld
    @2
    vy
    cv
    #
    @13
    wcel
    vz
    cv
    #
    @13
    wcel
    wa
    wa
    @23
    @24
    @5
    cplusg
    cfv
    co
    eqidd
    @2
    @23
    @14
    wcel
    @24
    @14
    wcel
    wa
    vy
    vz
    @18
    @19
    @2
    @17
    @20
    @22
    simprd
    oveqdr
    mhmpropd
    eleqtrrd
    jca
    cR
    cY
    cF
    @5
    @6
    @11
    @21
    isrhm
    sylanbrc
end
