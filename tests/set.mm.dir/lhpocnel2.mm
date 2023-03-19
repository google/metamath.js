include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "coc.mm"
include "cfv.mm"
include "wbr.mm"
include "wn.mm"
include "eqid.mm"
include "lhpocnel.mm"
include "eleq1i.mm"
include "breq1i.mm"
include "notbii.mm"
include "anbi12i.mm"
include "sylibr.mm"

theorem lhpocnel2
  let cA: class A
  let cP: class P
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume lhpocnel2.l: |- .<_ = ( le ` K )
  assume lhpocnel2.a: |- A = ( Atoms ` K )
  assume lhpocnel2.h: |- H = ( LHyp ` K )
  assume lhpocnel2.p: |- P = ( ( oc ` K ) ` W )


  assert |- ( ( K e. HL /\ W e. H ) -> ( P e. A /\ -. P .<_ W ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cW
    cK
    coc
    cfv
    #
    cfv
    #
    cA
    wcel
    #
    @1
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    cA
    cH
    cK
    c.le
    @0
    cW
    lhpocnel2.l
    @0
    eqid
    lhpocnel2.a
    lhpocnel2.h
    lhpocnel
    @5
    @2
    @7
    @4
    cP
    @1
    cA
    lhpocnel2.p
    eleq1i
    @6
    @3
    cP
    @1
    cW
    c.le
    lhpocnel2.p
    breq1i
    notbii
    anbi12i
    sylibr
end
