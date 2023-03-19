include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "cjn.mm"
include "cfv.mm"
include "co.mm"
include "cp1.mm"
include "wceq.mm"
include "wrex.mm"
include "ccvr.mm"
include "eqid.mm"
include "lhp1cvr.mm"
include "cbs.mm"
include "wb.mm"
include "simpl.mm"
include "lhpbase.mm"
include "adantl.mm"
include "cops.mm"
include "hlop.mm"
include "op1cl.mm"
include "syl.mm"
include "adantr.mm"
include "cvrval3.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "reximi.mm"

theorem lhpexnle
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
  assert |- ( ( K e. HL /\ W e. H ) -> E. p e. A -. p .<_ W )

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
    vp
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    cW
    @3
    cK
    cjn
    cfv
    #
    co
    cK
    cp1
    cfv
    #
    wceq
    #
    wa
    #
    vp
    cA
    wrex
    #
    @4
    vp
    cA
    wrex
    @2
    cW
    @6
    cK
    ccvr
    cfv
    #
    wbr
    #
    @9
    chlt
    @10
    @6
    cH
    cK
    cW
    @6
    eqid
    #
    @10
    eqid
    #
    lhp2a.h
    lhp1cvr
    @2
    @0
    cW
    cK
    cbs
    cfv
    #
    wcel
    #
    @6
    @14
    wcel
    #
    @11
    @9
    wb
    @0
    @1
    simpl
    @1
    @15
    @0
    @14
    cH
    cK
    cW
    @14
    eqid
    #
    lhp2a.h
    lhpbase
    adantl
    @0
    @16
    @1
    @0
    cK
    cops
    wcel
    @16
    cK
    hlop
    @14
    @6
    cK
    @17
    @12
    op1cl
    syl
    adantr
    cA
    @14
    @10
    @5
    cK
    c.le
    cW
    @6
    vp
    @17
    lhp2a.l
    @5
    eqid
    @13
    lhp2a.a
    cvrval3
    syl3anc
    mpbid
    @8
    @4
    vp
    cA
    @4
    @7
    simpl
    reximi
    syl
end
