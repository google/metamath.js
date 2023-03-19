include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "simpr.mm"
include "cbs.mm"
include "wb.mm"
include "eqid.mm"
include "lhpbase.mm"
include "lhpoc.mm"
include "sylan2.mm"
include "mpbid.mm"

theorem lhpocat
  let cA: class A
  let cH: class H
  let cK: class K
  let c.pe: class ._|_
  let cW: class W
  assume lhpocat.o: |- ._|_ = ( oc ` K )
  assume lhpocat.a: |- A = ( Atoms ` K )
  assume lhpocat.h: |- H = ( LHyp ` K )


  assert |- ( ( K e. HL /\ W e. H ) -> ( ._|_ ` W ) e. A )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    @1
    cW
    c.pe
    cfv
    cA
    wcel
    #
    @0
    @1
    simpr
    @1
    @0
    cW
    cK
    cbs
    cfv
    #
    wcel
    @1
    @2
    wb
    @3
    cH
    cK
    cW
    @3
    eqid
    #
    lhpocat.h
    lhpbase
    cA
    @3
    cH
    cK
    c.pe
    cW
    @4
    lhpocat.o
    lhpocat.a
    lhpocat.h
    lhpoc
    sylan2
    mpbid
end
