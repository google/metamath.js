include "wcel.mm"
include "cngp.mm"
include "cnm.mm"
include "cfv.mm"
include "cabv.mm"
include "cnrg.mm"
include "cgrp.mm"
include "cds.mm"
include "cbs.mm"
include "cme.mm"
include "crg.mm"
include "abvrcl.mm"
include "ringgrp.mm"
include "syl.mm"
include "csg.mm"
include "ccom.mm"
include "eqid.mm"
include "tngds.mm"
include "abvmet.mm"
include "eqeltrrd.mm"
include "cr.mm"
include "wf.mm"
include "wa.mm"
include "wb.mm"
include "abvf.mm"
include "tngngp2.mm"
include "mpbir2and.mm"
include "wceq.mm"
include "reex.mm"
include "tngnm.mm"
include "syl2anc.mm"
include "eqidd.mm"
include "tngbas.mm"
include "cv.mm"
include "cplusg.mm"
include "tngplusg.mm"
include "oveqdr.mm"
include "cmulr.mm"
include "tngmulr.mm"
include "abvpropd.mm"
include "syl5eq.mm"
include "eleq12d.mm"
include "ibi.mm"
include "isnrg.mm"
include "sylanbrc.mm"

theorem tngnrg
  let cA: class A
  let cR: class R
  let cT: class T
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  assume tngnrg.t: |- T = ( R toNrmGrp F )
  assume tngnrg.a: |- A = ( AbsVal ` R )


  assert |- ( F e. A -> T e. NrmRing )

  proof
    cF
    cA
    wcel
    #
    cT
    cngp
    wcel
    #
    cT
    cnm
    cfv
    #
    cT
    cabv
    cfv
    #
    wcel
    #
    cT
    cnrg
    wcel
    @0
    @1
    cR
    cgrp
    wcel
    #
    cT
    cds
    cfv
    #
    cR
    cbs
    cfv
    #
    cme
    cfv
    #
    wcel
    #
    @0
    cR
    crg
    wcel
    @5
    cA
    cR
    cF
    tngnrg.a
    abvrcl
    cR
    ringgrp
    syl
    #
    @0
    cF
    cR
    csg
    cfv
    #
    ccom
    @6
    @8
    cT
    cR
    @11
    cF
    cA
    tngnrg.t
    @11
    eqid
    #
    tngds
    cA
    cR
    cF
    @11
    @7
    @7
    eqid
    #
    tngnrg.a
    @12
    abvmet
    eqeltrrd
    @0
    @7
    cr
    cF
    wf
    #
    @1
    @5
    @9
    wa
    wb
    cA
    @7
    cR
    cF
    tngnrg.a
    @13
    abvf
    #
    @6
    cT
    cR
    cF
    @7
    tngnrg.t
    @13
    @6
    eqid
    tngngp2
    syl
    mpbir2and
    @0
    @4
    @0
    cF
    @2
    cA
    @3
    @0
    @5
    @14
    cF
    @2
    wceq
    @10
    @15
    cr
    cT
    cR
    cF
    @7
    tngnrg.t
    @13
    reex
    tngnm
    syl2anc
    @0
    cA
    cR
    cabv
    cfv
    @3
    tngnrg.a
    @0
    vx
    vy
    @7
    cR
    cT
    @0
    @7
    eqidd
    @7
    cT
    cR
    cF
    cA
    tngnrg.t
    @13
    tngbas
    @0
    vx
    cv
    @7
    wcel
    vy
    cv
    @7
    wcel
    wa
    #
    vx
    vy
    cR
    cplusg
    cfv
    #
    cT
    cplusg
    cfv
    @17
    cT
    cR
    cF
    cA
    tngnrg.t
    @17
    eqid
    tngplusg
    oveqdr
    @0
    @16
    vx
    vy
    cR
    cmulr
    cfv
    #
    cT
    cmulr
    cfv
    cT
    @18
    cR
    cF
    cA
    tngnrg.t
    @18
    eqid
    tngmulr
    oveqdr
    abvpropd
    syl5eq
    eleq12d
    ibi
    @3
    cT
    @2
    @2
    eqid
    @3
    eqid
    isnrg
    sylanbrc
end
