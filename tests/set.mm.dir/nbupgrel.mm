include "cupgr.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "cnbgr.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "cpr.mm"
include "wb.mm"
include "cv.mm"
include "crab.mm"
include "nbupgr.mm"
include "eleq2d.mm"
include "wceq.mm"
include "preq2.mm"
include "eleq1d.mm"
include "elrab.mm"
include "syl6bb.mm"
include "adantr.mm"
include "eldifsn.mm"
include "biimpri.mm"
include "adantl.mm"
include "biantrurd.mm"
include "prcom.mm"
include "eleq1i.mm"
include "a1i.mm"
include "3bitr2d.mm"

theorem nbupgrel
  let cE: class E
  let cG: class G
  let cK: class K
  let cN: class N
  let cV: class V
  let ve: setvar e
  let vn: setvar n
  let cX: class X
  let vv: setvar v
  let vx: setvar x
  assume nbuhgr.v: |- V = ( Vtx ` G )
  assume nbuhgr.e: |- E = ( Edg ` G )


  assert |- ( ( ( G e. UPGraph /\ K e. V ) /\ ( N e. V /\ N =/= K ) ) -> ( N e. ( G NeighbVtx K ) <-> { N , K } e. E ) )

  proof
    cG
    cupgr
    wcel
    cK
    cV
    wcel
    wa
    #
    cN
    cV
    wcel
    cN
    cK
    wne
    wa
    #
    wa
    #
    cN
    cG
    cK
    cnbgr
    co
    #
    wcel
    #
    cN
    cV
    cK
    csn
    cdif
    #
    wcel
    #
    cK
    cN
    cpr
    #
    cE
    wcel
    #
    wa
    #
    @8
    cN
    cK
    cpr
    #
    cE
    wcel
    #
    @0
    @4
    @9
    wb
    @1
    @0
    @4
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
    @5
    crab
    #
    wcel
    @9
    @0
    @3
    @15
    cN
    vn
    cE
    cG
    cK
    cV
    nbuhgr.v
    nbuhgr.e
    nbupgr
    eleq2d
    @14
    @8
    vn
    cN
    @5
    @12
    cN
    wceq
    @13
    @7
    cE
    @12
    cN
    cK
    preq2
    eleq1d
    elrab
    syl6bb
    adantr
    @2
    @6
    @8
    @1
    @6
    @0
    @6
    @1
    cN
    cV
    cK
    eldifsn
    biimpri
    adantl
    biantrurd
    @8
    @11
    wb
    @2
    @7
    @10
    cE
    cK
    cN
    prcom
    eleq1i
    a1i
    3bitr2d
end
