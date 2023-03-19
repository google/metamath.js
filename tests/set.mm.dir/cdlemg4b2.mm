include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "cmee.mm"
include "wceq.mm"
include "eqid.mm"
include "trlval2.mm"
include "3com23.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "simp1.mm"
include "simp2l.mm"
include "ltrnel.mm"
include "cdleme0cq.mm"
include "syl12anc.mm"
include "eqtrd.mm"

theorem cdlemg4b2
  let cA: class A
  let cP: class P
  let cR: class R
  let cT: class T
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let vr: setvar r
  let cF: class F
  let cQ: class Q
  assume cdlemg4.l: |- .<_ = ( le ` K )
  assume cdlemg4.a: |- A = ( Atoms ` K )
  assume cdlemg4.h: |- H = ( LHyp ` K )
  assume cdlemg4.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg4.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemg4.j: |- .\/ = ( join ` K )
  assume cdlemg4b.v: |- V = ( R ` G )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ G e. T ) -> ( ( G ` P ) .\/ V ) = ( P .\/ ( G ` P ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
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
    cG
    cT
    wcel
    #
    w3a
    #
    cP
    cG
    cfv
    #
    cV
    c.or
    co
    @6
    cP
    @6
    c.or
    co
    #
    cW
    cK
    cmee
    cfv
    #
    co
    #
    c.or
    co
    #
    @7
    @5
    cV
    @9
    @6
    c.or
    @5
    cV
    cG
    cR
    cfv
    #
    @9
    cdlemg4b.v
    @0
    @4
    @3
    @11
    @9
    wceq
    cA
    cP
    cR
    cT
    cG
    cH
    c.or
    cK
    c.le
    @8
    cW
    cdlemg4.l
    cdlemg4.j
    @8
    eqid
    #
    cdlemg4.a
    cdlemg4.h
    cdlemg4.t
    cdlemg4.r
    trlval2
    3com23
    syl5eq
    oveq2d
    @5
    @0
    @1
    @6
    cA
    wcel
    @6
    cW
    c.le
    wbr
    wn
    wa
    #
    @10
    @7
    wceq
    @0
    @3
    @4
    simp1
    @0
    @1
    @2
    @4
    simp2l
    @0
    @4
    @3
    @13
    cA
    cP
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemg4.l
    cdlemg4.a
    cdlemg4.h
    cdlemg4.t
    ltrnel
    3com23
    cA
    cP
    @6
    @9
    cH
    c.or
    cK
    c.le
    @8
    cW
    cdlemg4.l
    cdlemg4.j
    @12
    cdlemg4.a
    cdlemg4.h
    @9
    eqid
    cdleme0cq
    syl12anc
    eqtrd
end
