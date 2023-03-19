include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cp1.mm"
include "cfv.mm"
include "ccvr.mm"
include "wbr.mm"
include "eqid.mm"
include "islhp2.mm"
include "1cvrco.mm"
include "bitrd.mm"

theorem lhpoc
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


  assert |- ( ( K e. HL /\ W e. B ) -> ( W e. H <-> ( ._|_ ` W ) e. A ) )

  proof
    cK
    chlt
    wcel
    cW
    cB
    wcel
    wa
    cW
    cH
    wcel
    cW
    cK
    cp1
    cfv
    #
    cK
    ccvr
    cfv
    #
    wbr
    cW
    c.pe
    cfv
    cA
    wcel
    chlt
    cB
    @1
    @0
    cH
    cK
    cW
    lhpoc.b
    @0
    eqid
    #
    @1
    eqid
    #
    lhpoc.h
    islhp2
    cA
    cB
    @1
    @0
    cK
    c.pe
    cW
    lhpoc.b
    @2
    lhpoc.o
    @3
    lhpoc.a
    1cvrco
    bitrd
end
