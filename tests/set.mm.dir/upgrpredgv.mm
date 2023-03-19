include "cupgr.mm"
include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "w3a.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "upgredg.mm"
include "3adant2.mm"
include "wo.mm"
include "wb.mm"
include "preq12bg.mm"
include "3ad2antl2.mm"
include "wi.mm"
include "eleq1.mm"
include "eqcoms.mm"
include "biimpd.mm"
include "im2anan9.mm"
include "com12.mm"
include "ancoms.mm"
include "jaod.mm"
include "adantl.mm"
include "sylbid.mm"
include "rexlimdvva.mm"
include "mpd.mm"

theorem upgrpredgv
  let cU: class U
  let cE: class E
  let cG: class G
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let vm: setvar m
  let vn: setvar n
  let cC: class C
  let vx: setvar x
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume upgredg.v: |- V = ( Vtx ` G )
  assume upgredg.e: |- E = ( Edg ` G )


  assert |- ( ( G e. UPGraph /\ ( M e. U /\ N e. W ) /\ { M , N } e. E ) -> ( M e. V /\ N e. V ) )

  proof
    cG
    cupgr
    wcel
    #
    cM
    cU
    wcel
    cN
    cW
    wcel
    wa
    #
    cM
    cN
    cpr
    #
    cE
    wcel
    #
    w3a
    #
    @2
    vm
    cv
    #
    vn
    cv
    #
    cpr
    wceq
    #
    vn
    cV
    wrex
    vm
    cV
    wrex
    #
    cM
    cV
    wcel
    #
    cN
    cV
    wcel
    #
    wa
    #
    @0
    @3
    @8
    @1
    @2
    cE
    cG
    cV
    vm
    vn
    upgredg.v
    upgredg.e
    upgredg
    3adant2
    @4
    @7
    @11
    vm
    vn
    cV
    cV
    @4
    @5
    cV
    wcel
    #
    @6
    cV
    wcel
    #
    wa
    #
    wa
    @7
    cM
    @5
    wceq
    #
    cN
    @6
    wceq
    #
    wa
    #
    cM
    @6
    wceq
    #
    cN
    @5
    wceq
    #
    wa
    #
    wo
    #
    @11
    @1
    @0
    @14
    @7
    @21
    wb
    @3
    cM
    cN
    @5
    @6
    cU
    cW
    cV
    cV
    preq12bg
    3ad2antl2
    @14
    @21
    @11
    wi
    @4
    @14
    @17
    @11
    @20
    @17
    @14
    @11
    @15
    @12
    @9
    @16
    @13
    @10
    @15
    @12
    @9
    @12
    @9
    wb
    @5
    cM
    @5
    cM
    cV
    eleq1
    eqcoms
    biimpd
    @16
    @13
    @10
    @13
    @10
    wb
    @6
    cN
    @6
    cN
    cV
    eleq1
    eqcoms
    biimpd
    im2anan9
    com12
    @13
    @12
    @20
    @11
    wi
    @20
    @13
    @12
    wa
    @11
    @18
    @13
    @9
    @19
    @12
    @10
    @18
    @13
    @9
    @13
    @9
    wb
    @6
    cM
    @6
    cM
    cV
    eleq1
    eqcoms
    biimpd
    @19
    @12
    @10
    @12
    @10
    wb
    @5
    cN
    @5
    cN
    cV
    eleq1
    eqcoms
    biimpd
    im2anan9
    com12
    ancoms
    jaod
    adantl
    sylbid
    rexlimdvva
    mpd
end
