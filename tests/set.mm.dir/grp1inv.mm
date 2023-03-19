include "wcel.mm"
include "csn.mm"
include "cminusg.mm"
include "cfv.mm"
include "wf.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "cgrp.mm"
include "grp1.mm"
include "cvv.mm"
include "cbs.mm"
include "snex.mm"
include "cop.mm"
include "grpbase.mm"
include "ax-mp.mm"
include "eqid.mm"
include "grpinvf.mm"
include "syl.mm"
include "wb.mm"
include "fsng.mm"
include "anidms.mm"
include "wa.mm"
include "simpr.mm"
include "cxp.mm"
include "restidsing.mm"
include "xpsng.mm"
include "syl5req.mm"
include "adantr.mm"
include "eqtrd.mm"
include "ex.mm"
include "sylbid.mm"
include "mpd.mm"

theorem grp1inv
  let cI: class I
  let cM: class M
  let cV: class V
  let ve: setvar e
  let vi: setvar i
  assume grp1.m: |- M = { <. ( Base ` ndx ) , { I } >. , <. ( +g ` ndx ) , { <. <. I , I >. , I >. } >. }


  assert |- ( I e. V -> ( invg ` M ) = ( _I |` { I } ) )

  proof
    cI
    cV
    wcel
    #
    cI
    csn
    #
    @1
    cM
    cminusg
    cfv
    #
    wf
    #
    @2
    cid
    @1
    cres
    #
    wceq
    #
    @0
    cM
    cgrp
    wcel
    @3
    cI
    cM
    cV
    grp1.m
    grp1
    @1
    cM
    @2
    @1
    cvv
    wcel
    @1
    cM
    cbs
    cfv
    wceq
    cI
    snex
    @1
    cI
    cI
    cop
    #
    cI
    cop
    csn
    cM
    cvv
    grp1.m
    grpbase
    ax-mp
    @2
    eqid
    grpinvf
    syl
    @0
    @3
    @2
    @6
    csn
    #
    wceq
    #
    @5
    @0
    @3
    @8
    wb
    cI
    cI
    cV
    cV
    @2
    fsng
    anidms
    @0
    @8
    @5
    @0
    @8
    wa
    @2
    @7
    @4
    @0
    @8
    simpr
    @0
    @7
    @4
    wceq
    @8
    @0
    @4
    @1
    @1
    cxp
    #
    @7
    cI
    restidsing
    @0
    @9
    @7
    wceq
    cI
    cI
    cV
    cV
    xpsng
    anidms
    syl5req
    adantr
    eqtrd
    ex
    sylbid
    mpd
end
