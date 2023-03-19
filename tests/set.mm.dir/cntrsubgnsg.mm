include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "csg.mm"
include "wral.mm"
include "cbs.mm"
include "cnsg.mm"
include "simpl.mm"
include "ccntz.mm"
include "wceq.mm"
include "simplr.mm"
include "simprr.mm"
include "sseldd.mm"
include "ccntr.mm"
include "eqid.mm"
include "cntrval.mm"
include "eqtr4i.mm"
include "syl6eleqr.mm"
include "simprl.mm"
include "cntzi.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "cgrp.mm"
include "subgrcl.mm"
include "ad2antrr.mm"
include "subgss.mm"
include "grppncan.mm"
include "syl3anc.mm"
include "eqtr3d.mm"
include "eqeltrd.mm"
include "ralrimivva.mm"
include "isnsg3.mm"
include "sylanbrc.mm"

theorem cntrsubgnsg
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  assume cntrnsg.z: |- Z = ( Cntr ` M )


  assert |- ( ( X e. ( SubGrp ` M ) /\ X C_ Z ) -> X e. ( NrmSGrp ` M ) )

  proof
    cX
    cM
    csubg
    cfv
    wcel
    #
    cX
    cZ
    wss
    #
    wa
    #
    @0
    vx
    cv
    #
    vy
    cv
    #
    cM
    cplusg
    cfv
    #
    co
    #
    @3
    cM
    csg
    cfv
    #
    co
    #
    cX
    wcel
    #
    vy
    cX
    wral
    vx
    cM
    cbs
    cfv
    #
    wral
    cX
    cM
    cnsg
    cfv
    wcel
    @0
    @1
    simpl
    @2
    @9
    vx
    vy
    @10
    cX
    @2
    @3
    @10
    wcel
    #
    @4
    cX
    wcel
    #
    wa
    #
    wa
    #
    @8
    @4
    cX
    @14
    @4
    @3
    @5
    co
    #
    @3
    @7
    co
    #
    @8
    @4
    @14
    @15
    @6
    @3
    @7
    @14
    @4
    @10
    cM
    ccntz
    cfv
    #
    cfv
    #
    wcel
    @11
    @15
    @6
    wceq
    @14
    @4
    cZ
    @18
    @14
    cX
    cZ
    @4
    @0
    @1
    @13
    simplr
    @2
    @11
    @12
    simprr
    #
    sseldd
    @18
    cM
    ccntr
    cfv
    cZ
    @10
    cM
    @17
    @10
    eqid
    #
    @17
    eqid
    #
    cntrval
    cntrnsg.z
    eqtr4i
    syl6eleqr
    @2
    @11
    @12
    simprl
    #
    @5
    @10
    cM
    @4
    @3
    @17
    @5
    eqid
    #
    @21
    cntzi
    syl2anc
    oveq1d
    @14
    cM
    cgrp
    wcel
    #
    @4
    @10
    wcel
    @11
    @16
    @4
    wceq
    @0
    @24
    @1
    @13
    cX
    cM
    subgrcl
    ad2antrr
    @14
    cX
    @10
    @4
    @0
    cX
    @10
    wss
    @1
    @13
    @10
    cX
    cM
    @20
    subgss
    ad2antrr
    @19
    sseldd
    @22
    @10
    @5
    cM
    @7
    @4
    @3
    @20
    @23
    @7
    eqid
    #
    grppncan
    syl3anc
    eqtr3d
    @19
    eqeltrd
    ralrimivva
    vx
    vy
    @5
    cX
    cM
    @7
    @10
    @20
    @23
    @25
    isnsg3
    sylanbrc
end
