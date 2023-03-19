include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "ccvr.mm"
include "cfv.mm"
include "cv.mm"
include "wn.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "simp1.mm"
include "simp3.mm"
include "simp2.mm"
include "3jca.mm"
include "eqid.mm"
include "llncvrlpln2.mm"
include "sylan.mm"
include "cbs.mm"
include "wb.mm"
include "simpl1.mm"
include "simpl3.mm"
include "llnbase.mm"
include "syl.mm"
include "simpl2.mm"
include "lplnbase.mm"
include "cvrval3.mm"
include "syl3anc.mm"
include "eqcom.mm"
include "anbi2i.mm"
include "rexbii.mm"
include "syl6bb.mm"
include "mpbid.mm"

theorem lplnexatN
  let cA: class A
  let cP: class P
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cN: class N
  let cX: class X
  let cY: class Y
  let vq: setvar q
  assume lplnexat.l: |- .<_ = ( le ` K )
  assume lplnexat.j: |- .\/ = ( join ` K )
  assume lplnexat.a: |- A = ( Atoms ` K )
  assume lplnexat.n: |- N = ( LLines ` K )
  assume lplnexat.p: |- P = ( LPlanes ` K )

  disjoint A q
  disjoint K q
  disjoint .<_ q
  disjoint Y q
  disjoint X q
  assert |- ( ( ( K e. HL /\ X e. P /\ Y e. N ) /\ Y .<_ X ) -> E. q e. A ( -. q .<_ Y /\ X = ( Y .\/ q ) ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cP
    wcel
    #
    cY
    cN
    wcel
    #
    w3a
    #
    cY
    cX
    c.le
    wbr
    #
    wa
    #
    cY
    cX
    cK
    ccvr
    cfv
    #
    wbr
    #
    vq
    cv
    #
    cY
    c.le
    wbr
    wn
    #
    cX
    cY
    @8
    c.or
    co
    #
    wceq
    #
    wa
    #
    vq
    cA
    wrex
    #
    @3
    @0
    @2
    @1
    w3a
    @4
    @7
    @3
    @0
    @2
    @1
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp3
    @0
    @1
    @2
    simp2
    3jca
    @6
    cP
    cK
    c.le
    cN
    cY
    cX
    lplnexat.l
    @6
    eqid
    #
    lplnexat.n
    lplnexat.p
    llncvrlpln2
    sylan
    @5
    @7
    @9
    @10
    cX
    wceq
    #
    wa
    #
    vq
    cA
    wrex
    #
    @13
    @5
    @0
    cY
    cK
    cbs
    cfv
    #
    wcel
    #
    cX
    @18
    wcel
    #
    @7
    @17
    wb
    @0
    @1
    @2
    @4
    simpl1
    @5
    @2
    @19
    @0
    @1
    @2
    @4
    simpl3
    @18
    cK
    cN
    cY
    @18
    eqid
    #
    lplnexat.n
    llnbase
    syl
    @5
    @1
    @20
    @0
    @1
    @2
    @4
    simpl2
    @18
    cP
    cK
    cX
    @21
    lplnexat.p
    lplnbase
    syl
    cA
    @18
    @6
    c.or
    cK
    c.le
    cY
    cX
    vq
    @21
    lplnexat.l
    lplnexat.j
    @14
    lplnexat.a
    cvrval3
    syl3anc
    @16
    @12
    vq
    cA
    @15
    @11
    @9
    @10
    cX
    eqcom
    anbi2i
    rexbii
    syl6bb
    mpbid
end
