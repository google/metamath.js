include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "cgrp.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "ccntz.mm"
include "wss.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cima.mm"
include "cuni.mm"
include "cmrc.mm"
include "cin.mm"
include "c0g.mm"
include "wceq.mm"
include "wa.mm"
include "w3a.mm"
include "cvv.mm"
include "wb.mm"
include "reldmdprd.mm"
include "brrelex2i.mm"
include "dmexg.mm"
include "syl.mm"
include "eqid.mm"
include "dmdprd.mm"
include "sylancl.mm"
include "ibi.mm"
include "simp2d.mm"

theorem dprdf
  let cS: class S
  let cG: class G
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  let cI: class I
  let cK: class K
  let cX: class X
  let cY: class Y
  let cZ: class Z


  assert |- ( G dom DProd S -> S : dom S --> ( SubGrp ` G ) )

  proof
    cG
    cS
    cdprd
    cdm
    #
    wbr
    #
    cG
    cgrp
    wcel
    #
    cS
    cdm
    #
    cG
    csubg
    cfv
    #
    cS
    wf
    #
    vx
    cv
    #
    cS
    cfv
    #
    vy
    cv
    cS
    cfv
    cG
    ccntz
    cfv
    #
    cfv
    wss
    vy
    @3
    @6
    csn
    cdif
    #
    wral
    @7
    cS
    @9
    cima
    cuni
    @4
    cmrc
    cfv
    #
    cfv
    cin
    cG
    c0g
    cfv
    #
    csn
    wceq
    wa
    vx
    @3
    wral
    #
    @1
    @2
    @5
    @12
    w3a
    #
    @1
    @3
    cvv
    wcel
    #
    @3
    @3
    wceq
    @1
    @13
    wb
    @1
    cS
    cvv
    wcel
    @14
    cG
    cS
    @0
    reldmdprd
    brrelex2i
    cS
    cvv
    dmexg
    syl
    @3
    eqid
    vx
    vy
    cS
    cG
    @3
    @10
    cvv
    @11
    @8
    @8
    eqid
    @11
    eqid
    @10
    eqid
    dmdprd
    sylancl
    ibi
    simp2d
end
