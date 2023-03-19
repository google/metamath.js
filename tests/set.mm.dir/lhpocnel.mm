include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wbr.mm"
include "wn.mm"
include "lhpocat.mm"
include "lhpocnle.mm"
include "jca.mm"

theorem lhpocnel
  let cA: class A
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let c.pe: class ._|_
  let cW: class W
  assume lhpocnel.l: |- .<_ = ( le ` K )
  assume lhpocnel.o: |- ._|_ = ( oc ` K )
  assume lhpocnel.a: |- A = ( Atoms ` K )
  assume lhpocnel.h: |- H = ( LHyp ` K )


  assert |- ( ( K e. HL /\ W e. H ) -> ( ( ._|_ ` W ) e. A /\ -. ( ._|_ ` W ) .<_ W ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cW
    c.pe
    cfv
    #
    cA
    wcel
    @0
    cW
    c.le
    wbr
    wn
    cA
    cH
    cK
    c.pe
    cW
    lhpocnel.o
    lhpocnel.a
    lhpocnel.h
    lhpocat
    cH
    cK
    c.le
    c.pe
    cW
    lhpocnel.l
    lhpocnel.o
    lhpocnel.h
    lhpocnle
    jca
end
