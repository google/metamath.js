include "cusgr.mm"
include "wcel.mm"
include "cnbgr.mm"
include "co.mm"
include "cv.mm"
include "cpr.mm"
include "cvtx.mm"
include "cfv.mm"
include "crab.mm"
include "eqid.mm"
include "nbusgr.mm"
include "eleq2d.mm"
include "wa.mm"
include "usgrpredgv.mm"
include "simprd.mm"
include "ex.mm"
include "pm4.71rd.mm"
include "wb.mm"
include "prcom.mm"
include "eleq1i.mm"
include "a1i.mm"
include "wceq.mm"
include "preq2.mm"
include "eleq1d.mm"
include "elrab.mm"
include "3bitr4rd.mm"
include "bitrd.mm"

theorem nbusgreledg
  let cE: class E
  let cG: class G
  let cK: class K
  let cN: class N
  let vn: setvar n
  assume nbusgreledg.e: |- E = ( Edg ` G )


  assert |- ( G e. USGraph -> ( N e. ( G NeighbVtx K ) <-> { N , K } e. E ) )

  proof
    cG
    cusgr
    wcel
    #
    cN
    cG
    cK
    cnbgr
    co
    #
    wcel
    cN
    cK
    vn
    cv
    #
    cpr
    #
    cE
    wcel
    #
    vn
    cG
    cvtx
    cfv
    #
    crab
    #
    wcel
    #
    cN
    cK
    cpr
    #
    cE
    wcel
    #
    @0
    @1
    @6
    cN
    vn
    cE
    cG
    cK
    @5
    @5
    eqid
    #
    nbusgreledg.e
    nbusgr
    eleq2d
    @0
    cK
    cN
    cpr
    #
    cE
    wcel
    #
    cN
    @5
    wcel
    #
    @12
    wa
    #
    @9
    @7
    @0
    @12
    @13
    @0
    @12
    @13
    @0
    @12
    wa
    cK
    @5
    wcel
    @13
    cE
    cG
    cK
    cN
    @5
    nbusgreledg.e
    @10
    usgrpredgv
    simprd
    ex
    pm4.71rd
    @9
    @12
    wb
    @0
    @8
    @11
    cE
    cN
    cK
    prcom
    eleq1i
    a1i
    @7
    @14
    wb
    @0
    @4
    @12
    vn
    cN
    @5
    @2
    cN
    wceq
    @3
    @11
    cE
    @2
    cN
    cK
    preq2
    eleq1d
    elrab
    a1i
    3bitr4rd
    bitrd
end
