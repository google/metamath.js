include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wceq.mm"
include "simprr.mm"
include "cal.mm"
include "cbs.mm"
include "cfv.mm"
include "wb.mm"
include "hlatl.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "eqid.mm"
include "lhpbase.mm"
include "ad2antlr.mm"
include "atnle.mm"
include "syl3anc.mm"
include "mpbid.mm"

theorem lhpmat
  let cA: class A
  let cP: class P
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let c.0: class .0.
  assume lhpmat.l: |- .<_ = ( le ` K )
  assume lhpmat.m: |- ./\ = ( meet ` K )
  assume lhpmat.z: |- .0. = ( 0. ` K )
  assume lhpmat.a: |- A = ( Atoms ` K )
  assume lhpmat.h: |- H = ( LHyp ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) ) -> ( P ./\ W ) = .0. )

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
    #
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    wa
    #
    @4
    cP
    cW
    c.an
    co
    c.0
    wceq
    #
    @2
    @3
    @4
    simprr
    @6
    cK
    cal
    wcel
    #
    @3
    cW
    cK
    cbs
    cfv
    #
    wcel
    #
    @4
    @7
    wb
    @0
    @8
    @1
    @5
    cK
    hlatl
    ad2antrr
    @2
    @3
    @4
    simprl
    @1
    @10
    @0
    @5
    @9
    cH
    cK
    cW
    @9
    eqid
    #
    lhpmat.h
    lhpbase
    ad2antlr
    cA
    @9
    cP
    cK
    c.le
    c.an
    cW
    c.0
    @11
    lhpmat.l
    lhpmat.m
    lhpmat.z
    lhpmat.a
    atnle
    syl3anc
    mpbid
end
