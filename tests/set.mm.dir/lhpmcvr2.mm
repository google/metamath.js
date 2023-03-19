include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "ccvr.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "eqid.mm"
include "lhpmcvr.mm"
include "wb.mm"
include "simpll.mm"
include "simprl.mm"
include "lhpbase.mm"
include "ad2antlr.mm"
include "cvrval5.mm"
include "syl3anc.mm"
include "mpbid.mm"

theorem lhpmcvr2
  let cA: class A
  let cB: class B
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let vp: setvar p
  assume lhpmcvr2.b: |- B = ( Base ` K )
  assume lhpmcvr2.l: |- .<_ = ( le ` K )
  assume lhpmcvr2.j: |- .\/ = ( join ` K )
  assume lhpmcvr2.m: |- ./\ = ( meet ` K )
  assume lhpmcvr2.a: |- A = ( Atoms ` K )
  assume lhpmcvr2.h: |- H = ( LHyp ` K )

  disjoint A p
  disjoint B p
  disjoint K p
  disjoint .<_ p
  disjoint ./\ p
  disjoint X p
  disjoint W p
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ -. X .<_ W ) ) -> E. p e. A ( -. p .<_ W /\ ( p .\/ ( X ./\ W ) ) = X ) )

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
    cX
    cB
    wcel
    #
    cX
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    wa
    #
    cX
    cW
    c.an
    co
    #
    cX
    cK
    ccvr
    cfv
    #
    wbr
    #
    vp
    cv
    #
    cW
    c.le
    wbr
    wn
    @10
    @7
    c.or
    co
    cX
    wceq
    wa
    vp
    cA
    wrex
    #
    cB
    @8
    cH
    cK
    c.le
    c.an
    cW
    cX
    lhpmcvr2.b
    lhpmcvr2.l
    lhpmcvr2.m
    @8
    eqid
    #
    lhpmcvr2.h
    lhpmcvr
    @6
    @0
    @3
    cW
    cB
    wcel
    #
    @9
    @11
    wb
    @0
    @1
    @5
    simpll
    @2
    @3
    @4
    simprl
    @1
    @13
    @0
    @5
    cB
    cH
    cK
    cW
    lhpmcvr2.b
    lhpmcvr2.h
    lhpbase
    ad2antlr
    cA
    cB
    @8
    c.or
    cK
    c.le
    c.an
    cX
    cW
    vp
    lhpmcvr2.b
    lhpmcvr2.l
    lhpmcvr2.j
    lhpmcvr2.m
    @12
    lhpmcvr2.a
    cvrval5
    syl3anc
    mpbid
end
