include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wb.mm"
include "cops.mm"
include "hlop.mm"
include "opoccl.mm"
include "sylan.mm"
include "lhpoc.mm"
include "syldan.mm"
include "wceq.mm"
include "opococ.mm"
include "eleq1d.mm"
include "bitr2d.mm"

theorem lhpoc2N
  let cA: class A
  let cB: class B
  let cH: class H
  let cK: class K
  let c.pe: class ._|_
  let cW: class W
  assume lhpoc.b: |- B = ( Base ` K )
  assume lhpoc.o: |- ._|_ = ( oc ` K )
  assume lhpoc.a: |- A = ( Atoms ` K )
  assume lhpoc.h: |- H = ( LHyp ` K )


  assert |- ( ( K e. HL /\ W e. B ) -> ( W e. A <-> ( ._|_ ` W ) e. H ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cB
    wcel
    #
    wa
    #
    cW
    c.pe
    cfv
    #
    cH
    wcel
    #
    @3
    c.pe
    cfv
    #
    cA
    wcel
    #
    cW
    cA
    wcel
    @0
    @1
    @3
    cB
    wcel
    #
    @4
    @6
    wb
    @0
    cK
    cops
    wcel
    #
    @1
    @7
    cK
    hlop
    #
    cB
    cK
    c.pe
    cW
    lhpoc.b
    lhpoc.o
    opoccl
    sylan
    cA
    cB
    cH
    cK
    c.pe
    @3
    lhpoc.b
    lhpoc.o
    lhpoc.a
    lhpoc.h
    lhpoc
    syldan
    @2
    @5
    cW
    cA
    @0
    @8
    @1
    @5
    cW
    wceq
    @9
    cB
    cK
    c.pe
    cW
    lhpoc.b
    lhpoc.o
    opococ
    sylan
    eleq1d
    bitr2d
end
