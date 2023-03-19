include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "cdlemg4f.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp21.mm"
include "simp22l.mm"
include "eqid.mm"
include "cdleme0cp.mm"
include "syl22anc.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem cdlemg4g
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  let vr: setvar r
  assume cdlemg4.l: |- .<_ = ( le ` K )
  assume cdlemg4.a: |- A = ( Atoms ` K )
  assume cdlemg4.h: |- H = ( LHyp ` K )
  assume cdlemg4.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg4.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemg4.j: |- .\/ = ( join ` K )
  assume cdlemg4b.v: |- V = ( R ` G )
  assume cdlemg4.m: |- ./\ = ( meet ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ F e. T ) /\ ( G e. T /\ -. Q .<_ ( P .\/ V ) /\ ( F ` ( G ` P ) ) = P ) ) -> ( F ` ( G ` Q ) ) = ( ( Q .\/ V ) ./\ ( P .\/ Q ) ) )

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
    cP
    cW
    c.le
    wbr
    wn
    wa
    #
    cQ
    cA
    wcel
    #
    cQ
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cF
    cT
    wcel
    #
    w3a
    #
    cG
    cT
    wcel
    cQ
    cP
    cV
    c.or
    co
    c.le
    wbr
    wn
    cP
    cG
    cfv
    cF
    cfv
    cP
    wceq
    w3a
    #
    w3a
    #
    cQ
    cG
    cfv
    cF
    cfv
    cQ
    cV
    c.or
    co
    #
    cP
    cP
    cQ
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    @11
    @12
    c.an
    co
    cA
    cP
    cQ
    cR
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    cdlemg4.l
    cdlemg4.a
    cdlemg4.h
    cdlemg4.t
    cdlemg4.r
    cdlemg4.j
    cdlemg4b.v
    cdlemg4.m
    cdlemg4f
    @10
    @14
    @12
    @11
    c.an
    @10
    @0
    @1
    @3
    @4
    @14
    @12
    wceq
    @0
    @1
    @8
    @9
    simp1l
    @0
    @1
    @8
    @9
    simp1r
    @2
    @3
    @6
    @7
    @9
    simp21
    @4
    @5
    @3
    @7
    @2
    @9
    simp22l
    cA
    cP
    cQ
    @13
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg4.l
    cdlemg4.j
    cdlemg4.m
    cdlemg4.a
    cdlemg4.h
    @13
    eqid
    cdleme0cp
    syl22anc
    oveq2d
    eqtrd
end
