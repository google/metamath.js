include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "cmee.mm"
include "wceq.mm"
include "eqid.mm"
include "trlval2.mm"
include "3com23.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "simp1.mm"
include "simp2.mm"
include "ltrnel.mm"
include "simpld.mm"
include "cdleme0cp.mm"
include "syl12anc.mm"
include "eqtrd.mm"

theorem cdlemg4b1
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ G e. T ) -> ( P .\/ V ) = ( P .\/ ( G ` P ) ) )

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
    cP
    cW
    c.le
    wbr
    wn
    wa
    #
    cG
    cT
    wcel
    #
    w3a
    #
    cP
    cV
    c.or
    co
    cP
    cP
    cP
    cG
    cfv
    #
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
    @5
    @3
    cV
    @7
    cP
    c.or
    @3
    cV
    cG
    cR
    cfv
    #
    @7
    cdlemg4b.v
    @0
    @2
    @1
    @9
    @7
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
    @6
    cW
    cdlemg4.l
    cdlemg4.j
    @6
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
    @3
    @0
    @1
    @4
    cA
    wcel
    #
    @8
    @5
    wceq
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    @0
    @2
    @1
    @11
    @0
    @2
    @1
    w3a
    @11
    @4
    cW
    c.le
    wbr
    wn
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
    simpld
    3com23
    cA
    cP
    @4
    @7
    cH
    c.or
    cK
    c.le
    @6
    cW
    cdlemg4.l
    cdlemg4.j
    @10
    cdlemg4.a
    cdlemg4.h
    @7
    eqid
    cdleme0cp
    syl12anc
    eqtrd
end
