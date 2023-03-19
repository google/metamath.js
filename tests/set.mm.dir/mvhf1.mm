include "cmfs.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wf1.mm"
include "mvhf.mm"
include "wa.mm"
include "cmty.mm"
include "cs1.mm"
include "cop.mm"
include "wb.mm"
include "eqid.mm"
include "mvhval.mm"
include "eqeqan12d.mm"
include "adantl.mm"
include "fvex.mm"
include "cvv.mm"
include "cword.mm"
include "s1cli.mm"
include "elexi.mm"
include "opth.mm"
include "simprbi.mm"
include "s111.mm"
include "syl5ib.mm"
include "sylbid.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"

theorem mvhf1
  let cT: class T
  let cE: class E
  let cH: class H
  let cV: class V
  let vv: setvar v
  let vw: setvar w
  assume mvhf.v: |- V = ( mVR ` T )
  assume mvhf.e: |- E = ( mEx ` T )
  assume mvhf.h: |- H = ( mVH ` T )


  assert |- ( T e. mFS -> H : V -1-1-> E )

  proof
    cT
    cmfs
    wcel
    #
    cV
    cE
    cH
    wf
    vv
    cv
    #
    cH
    cfv
    #
    vw
    cv
    #
    cH
    cfv
    #
    wceq
    #
    @1
    @3
    wceq
    #
    wi
    #
    vw
    cV
    wral
    vv
    cV
    wral
    cV
    cE
    cH
    wf1
    cT
    cE
    cH
    cV
    mvhf.v
    mvhf.e
    mvhf.h
    mvhf
    @0
    @7
    vv
    vw
    cV
    cV
    @0
    @1
    cV
    wcel
    #
    @3
    cV
    wcel
    #
    wa
    #
    wa
    #
    @5
    @1
    cT
    cmty
    cfv
    #
    cfv
    #
    @1
    cs1
    #
    cop
    #
    @3
    @12
    cfv
    #
    @3
    cs1
    #
    cop
    #
    wceq
    #
    @6
    @10
    @5
    @19
    wb
    @0
    @8
    @9
    @2
    @15
    @4
    @18
    cT
    cH
    cV
    @1
    @12
    mvhf.v
    @12
    eqid
    #
    mvhf.h
    mvhval
    cT
    cH
    cV
    @3
    @12
    mvhf.v
    @20
    mvhf.h
    mvhval
    eqeqan12d
    adantl
    @19
    @14
    @17
    wceq
    #
    @11
    @6
    @19
    @13
    @16
    wceq
    @21
    @13
    @14
    @16
    @17
    @1
    @12
    fvex
    @14
    cvv
    cword
    @1
    s1cli
    elexi
    opth
    simprbi
    @10
    @21
    @6
    wb
    @0
    cV
    @1
    @3
    s111
    adantl
    syl5ib
    sylbid
    ralrimivva
    vv
    vw
    cV
    cE
    cH
    dff13
    sylanbrc
end
