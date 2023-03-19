include "cdprd.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "cdm.mm"
include "wbr.mm"
include "cgsu.mm"
include "wceq.mm"
include "c0g.mm"
include "cfv.mm"
include "cfsupp.mm"
include "cixp.mm"
include "crab.mm"
include "wrex.mm"
include "wa.mm"
include "wb.mm"
include "eqid.mm"
include "eldprd.mm"
include "ax-mp.mm"
include "cvv.mm"
include "ccntz.mm"
include "cmnd.mm"
include "cgrp.mm"
include "dprdgrp.mm"
include "grpmnd.mm"
include "syl.mm"
include "adantr.mm"
include "reldmdprd.mm"
include "brrelex2i.mm"
include "dmexg.mm"
include "simpl.mm"
include "eqidd.mm"
include "simpr.mm"
include "dprdff.mm"
include "dprdfcntz.mm"
include "dprdffsupp.mm"
include "gsumzcl.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "imp.mm"
include "sylbi.mm"
include "ssriv.mm"

theorem dprdssv
  let cB: class B
  let cS: class S
  let cG: class G
  let vf: setvar f
  let vx: setvar x
  let vh: setvar h
  let vi: setvar i
  assume dprdssv.b: |- B = ( Base ` G )


  assert |- ( G DProd S ) C_ B

  proof
    vx
    cG
    cS
    cdprd
    co
    #
    cB
    vx
    cv
    #
    @0
    wcel
    #
    cG
    cS
    cdprd
    cdm
    #
    wbr
    #
    @1
    cG
    vf
    cv
    #
    cgsu
    co
    #
    wceq
    #
    vf
    vh
    cv
    cG
    c0g
    cfv
    #
    cfsupp
    wbr
    vh
    vi
    cS
    cdm
    #
    vi
    cv
    cS
    cfv
    cixp
    crab
    #
    wrex
    #
    wa
    #
    @1
    cB
    wcel
    #
    @9
    @9
    wceq
    @2
    @12
    wb
    @9
    eqid
    @1
    cS
    vf
    vh
    vi
    cG
    @9
    @10
    @8
    @8
    eqid
    #
    @10
    eqid
    #
    eldprd
    ax-mp
    @4
    @11
    @13
    @4
    @7
    @13
    vf
    @10
    @4
    @5
    @10
    wcel
    #
    wa
    #
    @13
    @7
    @6
    cB
    wcel
    @17
    @9
    cB
    @5
    cG
    cvv
    @8
    cG
    ccntz
    cfv
    #
    dprdssv.b
    @14
    @18
    eqid
    #
    @4
    cG
    cmnd
    wcel
    #
    @16
    @4
    cG
    cgrp
    wcel
    @20
    cS
    cG
    dprdgrp
    cG
    grpmnd
    syl
    adantr
    @4
    @9
    cvv
    wcel
    #
    @16
    @4
    cS
    cvv
    wcel
    @21
    cG
    cS
    @3
    reldmdprd
    brrelex2i
    cS
    cvv
    dmexg
    syl
    adantr
    @17
    cB
    cS
    vh
    vi
    @5
    cG
    @9
    @10
    @8
    @15
    @4
    @16
    simpl
    #
    @17
    @9
    eqidd
    #
    @4
    @16
    simpr
    #
    dprdssv.b
    dprdff
    @17
    cS
    vh
    vi
    @5
    cG
    @9
    @10
    @8
    @18
    @15
    @22
    @23
    @24
    @19
    dprdfcntz
    @17
    cS
    vh
    vi
    @5
    cG
    @9
    @10
    @8
    @15
    @22
    @23
    @24
    dprdffsupp
    gsumzcl
    @1
    @6
    cB
    eleq1
    syl5ibrcom
    rexlimdva
    imp
    sylbi
    ssriv
end
