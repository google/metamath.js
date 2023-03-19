include "wcel.mm"
include "cid.mm"
include "cres.mm"
include "cop.mm"
include "cusgr.mm"
include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "cvtx.mm"
include "cpw.mm"
include "crab.mm"
include "wf1.mm"
include "usgrexilem.mm"
include "cvv.mm"
include "cusgrexilem1.mm"
include "opiedgfv.mm"
include "mpdan.mm"
include "dmeqd.mm"
include "opvtxfv.mm"
include "pweqd.mm"
include "rabeqdv.mm"
include "f1eq123d.mm"
include "mpbird.mm"
include "wb.mm"
include "opex.mm"
include "eqid.mm"
include "isusgrs.mm"
include "mp1i.mm"

theorem usgrexi
  let vx: setvar x
  let cP: class P
  let cV: class V
  let cW: class W
  assume usgrexi.p: |- P = { x e. ~P V | ( # ` x ) = 2 }

  disjoint V x
  disjoint P x
  disjoint W x
  assert |- ( V e. W -> <. V , ( _I |` P ) >. e. USGraph )

  proof
    cV
    cW
    wcel
    #
    cV
    cid
    cP
    cres
    #
    cop
    #
    cusgr
    wcel
    #
    @2
    ciedg
    cfv
    #
    cdm
    #
    vx
    cv
    chash
    cfv
    c2
    wceq
    #
    vx
    @2
    cvtx
    cfv
    #
    cpw
    #
    crab
    #
    @4
    wf1
    #
    @0
    @10
    @1
    cdm
    #
    @6
    vx
    cV
    cpw
    #
    crab
    #
    @1
    wf1
    vx
    cP
    cV
    cW
    usgrexi.p
    usgrexilem
    @0
    @5
    @11
    @9
    @13
    @4
    @1
    @0
    @1
    cvv
    wcel
    #
    @4
    @1
    wceq
    vx
    cP
    cV
    cW
    usgrexi.p
    cusgrexilem1
    #
    @1
    cV
    cW
    cvv
    opiedgfv
    mpdan
    #
    @0
    @4
    @1
    @16
    dmeqd
    @0
    @6
    vx
    @8
    @12
    @0
    @7
    cV
    @0
    @14
    @7
    cV
    wceq
    @15
    @1
    cV
    cW
    cvv
    opvtxfv
    mpdan
    pweqd
    rabeqdv
    f1eq123d
    mpbird
    @2
    cvv
    wcel
    @3
    @10
    wb
    @0
    cV
    @1
    opex
    vx
    cvv
    @4
    @2
    @7
    @7
    eqid
    @4
    eqid
    isusgrs
    mp1i
    mpbird
end
