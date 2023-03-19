include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cp0.mm"
include "wne.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "simpl.mm"
include "eqid.mm"
include "lhpbase.mm"
include "adantl.mm"
include "lhpn0.mm"
include "atle.mm"
include "syl3anc.mm"

theorem lhpexle
  let cA: class A
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vp: setvar p
  assume lhp2a.l: |- .<_ = ( le ` K )
  assume lhp2a.a: |- A = ( Atoms ` K )
  assume lhp2a.h: |- H = ( LHyp ` K )

  disjoint A p
  disjoint H p
  disjoint K p
  disjoint .<_ p
  disjoint W p
  assert |- ( ( K e. HL /\ W e. H ) -> E. p e. A p .<_ W )

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
    @0
    cW
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    cK
    cp0
    cfv
    #
    wne
    vp
    cv
    cW
    c.le
    wbr
    vp
    cA
    wrex
    @0
    @1
    simpl
    @1
    @3
    @0
    @2
    cH
    cK
    cW
    @2
    eqid
    #
    lhp2a.h
    lhpbase
    adantl
    cH
    cK
    cW
    @4
    @4
    eqid
    #
    lhp2a.h
    lhpn0
    cA
    @2
    cK
    c.le
    cW
    @4
    vp
    @5
    lhp2a.l
    @6
    lhp2a.a
    atle
    syl3anc
end
