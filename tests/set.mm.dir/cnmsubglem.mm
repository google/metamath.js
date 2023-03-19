include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wral.mm"
include "ccnfld.mm"
include "cinvr.mm"
include "wa.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "ssriv.mm"
include "c1.mm"
include "ne0ii.mm"
include "ralrimiva.mm"
include "cdiv.mm"
include "wceq.mm"
include "cnfldinv.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "jca.mm"
include "rgen.mm"
include "cabl.mm"
include "cgrp.mm"
include "w3a.mm"
include "wb.mm"
include "cnmgpabl.mm"
include "ablgrp.mm"
include "cbs.mm"
include "difss.mm"
include "cmgp.mm"
include "eqid.mm"
include "cnfldbas.mm"
include "mgpbas.mm"
include "ressbas2.mm"
include "ax-mp.mm"
include "cvv.mm"
include "cplusg.mm"
include "cnex.mm"
include "difexg.mm"
include "cnfldmul.mm"
include "mgpplusg.mm"
include "ressplusg.mm"
include "mp2b.mm"
include "cnfld0.mm"
include "cndrng.mm"
include "drngui.mm"
include "invrfval.mm"
include "issubg2.mm"
include "mpbir3an.mm"

theorem cnmsubglem
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cM: class M
  assume cnmgpabl.m: |- M = ( ( mulGrp ` CCfld ) |`s ( CC \ { 0 } ) )
  assume cnmsubglem.1: |- ( x e. A -> x e. CC )
  assume cnmsubglem.2: |- ( x e. A -> x =/= 0 )
  assume cnmsubglem.3: |- ( ( x e. A /\ y e. A ) -> ( x x. y ) e. A )
  assume cnmsubglem.4: |- 1 e. A
  assume cnmsubglem.5: |- ( x e. A -> ( 1 / x ) e. A )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint M x
  disjoint M y
  assert |- A e. ( SubGrp ` M )

  proof
    cA
    cM
    csubg
    cfv
    wcel
    #
    cA
    cc
    cc0
    csn
    #
    cdif
    #
    wss
    #
    cA
    c0
    wne
    #
    vx
    cv
    #
    vy
    cv
    cmul
    co
    cA
    wcel
    #
    vy
    cA
    wral
    #
    @5
    ccnfld
    cinvr
    cfv
    #
    cfv
    #
    cA
    wcel
    #
    wa
    #
    vx
    cA
    wral
    #
    vx
    cA
    @2
    @5
    cA
    wcel
    #
    @5
    cc
    wcel
    #
    @5
    cc0
    wne
    #
    @5
    @2
    wcel
    cnmsubglem.1
    cnmsubglem.2
    @5
    cc
    cc0
    eldifsn
    sylanbrc
    ssriv
    c1
    cA
    cnmsubglem.4
    ne0ii
    @11
    vx
    cA
    @13
    @7
    @10
    @13
    @6
    vy
    cA
    cnmsubglem.3
    ralrimiva
    @13
    @9
    c1
    @5
    cdiv
    co
    #
    cA
    @13
    @14
    @15
    @9
    @16
    wceq
    cnmsubglem.1
    cnmsubglem.2
    @5
    cnfldinv
    syl2anc
    cnmsubglem.5
    eqeltrd
    jca
    rgen
    cM
    cabl
    wcel
    cM
    cgrp
    wcel
    @0
    @3
    @4
    @12
    w3a
    wb
    cM
    cnmgpabl.m
    cnmgpabl
    cM
    ablgrp
    vx
    vy
    @2
    cmul
    cA
    cM
    @8
    @2
    cc
    wss
    @2
    cM
    cbs
    cfv
    wceq
    cc
    @1
    difss
    @2
    cc
    cM
    ccnfld
    cmgp
    cfv
    #
    cnmgpabl.m
    cc
    ccnfld
    @17
    @17
    eqid
    #
    cnfldbas
    mgpbas
    ressbas2
    ax-mp
    cc
    cvv
    wcel
    @2
    cvv
    wcel
    cmul
    cM
    cplusg
    cfv
    wceq
    cnex
    cc
    @1
    cvv
    difexg
    @2
    cmul
    @17
    cM
    cvv
    cnmgpabl.m
    ccnfld
    cmul
    @17
    @18
    cnfldmul
    mgpplusg
    ressplusg
    mp2b
    ccnfld
    @2
    cM
    @8
    cc
    ccnfld
    cc0
    cnfldbas
    cnfld0
    cndrng
    drngui
    cnmgpabl.m
    @8
    eqid
    invrfval
    issubg2
    mp2b
    mpbir3an
end
