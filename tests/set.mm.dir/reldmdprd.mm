include "cgrp.mm"
include "cv.mm"
include "cdm.mm"
include "csubg.mm"
include "cfv.mm"
include "wf.mm"
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
include "cab.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cixp.mm"
include "crab.mm"
include "cgsu.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "cdprd.mm"
include "df-dprd.mm"
include "reldmmpt2.mm"

theorem reldmdprd
  let vg: setvar g
  let vh: setvar h
  let c.0: class .0.
  let vf: setvar f
  let vi: setvar i
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  let cI: class I
  let cK: class K
  let cZ: class Z
  let wph: wff ph
  let cS: class S
  let cV: class V


  assert |- Rel dom DProd

  proof
    vg
    vs
    cgrp
    vh
    cv
    #
    cdm
    #
    vg
    cv
    #
    csubg
    cfv
    #
    @0
    wf
    vx
    cv
    #
    @0
    cfv
    #
    vy
    cv
    @0
    cfv
    @2
    ccntz
    cfv
    cfv
    wss
    vy
    @1
    @4
    csn
    cdif
    #
    wral
    @5
    @0
    @6
    cima
    cuni
    @3
    cmrc
    cfv
    cfv
    cin
    @2
    c0g
    cfv
    #
    csn
    wceq
    wa
    vx
    @1
    wral
    wa
    vh
    cab
    vf
    @0
    @7
    cfsupp
    wbr
    vh
    vx
    vs
    cv
    #
    cdm
    @4
    @8
    cfv
    cixp
    crab
    @2
    vf
    cv
    cgsu
    co
    cmpt
    crn
    cdprd
    vx
    vy
    vf
    vg
    vh
    vs
    df-dprd
    reldmmpt2
end
