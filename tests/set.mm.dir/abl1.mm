include "wcel.mm"
include "cgrp.mm"
include "cv.mm"
include "cop.mm"
include "csn.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cabl.mm"
include "grp1.mm"
include "eqidd.mm"
include "oveq1.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "ralbidv.mm"
include "ralsng.mm"
include "bitrd.mm"
include "mpbird.mm"
include "cvv.mm"
include "cbs.mm"
include "cfv.mm"
include "snex.mm"
include "grpbase.mm"
include "ax-mp.mm"
include "cplusg.mm"
include "grpplusg.mm"
include "isabl2.mm"
include "sylanbrc.mm"

theorem abl1
  let cI: class I
  let cM: class M
  let cV: class V
  let va: setvar a
  let vb: setvar b
  assume abl1.m: |- M = { <. ( Base ` ndx ) , { I } >. , <. ( +g ` ndx ) , { <. <. I , I >. , I >. } >. }


  assert |- ( I e. V -> M e. Abel )

  proof
    cI
    cV
    wcel
    #
    cM
    cgrp
    wcel
    va
    cv
    #
    vb
    cv
    #
    cI
    cI
    cop
    cI
    cop
    #
    csn
    #
    co
    #
    @2
    @1
    @4
    co
    #
    wceq
    #
    vb
    cI
    csn
    #
    wral
    #
    va
    @8
    wral
    #
    cM
    cabl
    wcel
    cI
    cM
    cV
    abl1.m
    grp1
    @0
    @10
    cI
    cI
    @4
    co
    #
    @11
    wceq
    #
    @0
    @11
    eqidd
    @0
    @10
    cI
    @2
    @4
    co
    #
    @2
    cI
    @4
    co
    #
    wceq
    #
    vb
    @8
    wral
    #
    @12
    @9
    @16
    va
    cI
    cV
    @1
    cI
    wceq
    #
    @7
    @15
    vb
    @8
    @17
    @5
    @13
    @6
    @14
    @1
    cI
    @2
    @4
    oveq1
    @1
    cI
    @2
    @4
    oveq2
    eqeq12d
    ralbidv
    ralsng
    @15
    @12
    vb
    cI
    cV
    @2
    cI
    wceq
    @13
    @11
    @14
    @11
    @2
    cI
    cI
    @4
    oveq2
    @2
    cI
    cI
    @4
    oveq1
    eqeq12d
    ralsng
    bitrd
    mpbird
    va
    vb
    @8
    @4
    cM
    @8
    cvv
    wcel
    @8
    cM
    cbs
    cfv
    wceq
    cI
    snex
    @8
    @4
    cM
    cvv
    abl1.m
    grpbase
    ax-mp
    @4
    cvv
    wcel
    @4
    cM
    cplusg
    cfv
    wceq
    @3
    snex
    @8
    @4
    cM
    cvv
    abl1.m
    grpplusg
    ax-mp
    isabl2
    sylanbrc
end
