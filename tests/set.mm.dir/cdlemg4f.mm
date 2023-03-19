include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "cdlemg4e.mm"
include "simp1.mm"
include "simp21.mm"
include "simp23.mm"
include "simp31.mm"
include "simp33.mm"
include "cdlemg4a.mm"
include "syl131anc.mm"
include "syl6reqr.mm"
include "oveq2d.mm"
include "simp22.mm"
include "cdlemg4b12.mm"
include "syl3anc.mm"
include "eqtr3d.mm"
include "eqid.mm"
include "cdlemg2m.mm"
include "syl121anc.mm"
include "oveq12d.mm"
include "eqtrd.mm"

theorem cdlemg4f
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ F e. T ) /\ ( G e. T /\ -. Q .<_ ( P .\/ V ) /\ ( F ` ( G ` P ) ) = P ) ) -> ( F ` ( G ` Q ) ) = ( ( Q .\/ V ) ./\ ( P .\/ ( ( P .\/ Q ) ./\ W ) ) ) )

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
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
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
    #
    cQ
    cP
    cV
    c.or
    co
    c.le
    wbr
    wn
    #
    cP
    cG
    cfv
    #
    cF
    cfv
    #
    cP
    wceq
    #
    w3a
    #
    w3a
    #
    cQ
    cG
    cfv
    #
    cF
    cfv
    @12
    cF
    cR
    cfv
    #
    c.or
    co
    #
    @8
    @7
    @12
    c.or
    co
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
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
    cW
    c.an
    co
    #
    c.or
    co
    #
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
    cdlemg4e
    @11
    @14
    @17
    @16
    @19
    c.an
    @11
    @12
    cV
    c.or
    co
    #
    @14
    @17
    @11
    cV
    @13
    @12
    c.or
    @11
    @13
    cG
    cR
    cfv
    #
    cV
    @11
    @0
    @1
    @3
    @5
    @9
    @13
    @21
    wceq
    @0
    @4
    @10
    simp1
    #
    @0
    @1
    @2
    @3
    @10
    simp21
    #
    @0
    @1
    @2
    @3
    @10
    simp23
    @0
    @4
    @5
    @6
    @9
    simp31
    #
    @0
    @4
    @5
    @6
    @9
    simp33
    #
    cA
    cP
    cR
    cT
    cF
    cG
    cH
    cK
    c.le
    cW
    cdlemg4.l
    cdlemg4.a
    cdlemg4.h
    cdlemg4.t
    cdlemg4.r
    cdlemg4a
    syl131anc
    cdlemg4b.v
    syl6reqr
    oveq2d
    @11
    @0
    @2
    @5
    @20
    @17
    wceq
    @22
    @0
    @1
    @2
    @3
    @10
    simp22
    #
    @24
    cA
    cQ
    cR
    cT
    cG
    cH
    c.or
    cK
    c.le
    cV
    cW
    cdlemg4.l
    cdlemg4.a
    cdlemg4.h
    cdlemg4.t
    cdlemg4.r
    cdlemg4.j
    cdlemg4b.v
    cdlemg4b12
    syl3anc
    eqtr3d
    @11
    @8
    cP
    @15
    @18
    c.or
    @25
    @11
    @0
    @1
    @2
    @5
    @15
    @18
    wceq
    @22
    @23
    @26
    @24
    cA
    cP
    cQ
    cT
    @18
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg4.h
    cdlemg4.t
    cdlemg4.l
    cdlemg4.j
    cdlemg4.a
    cdlemg4.m
    @18
    eqid
    cdlemg2m
    syl121anc
    oveq12d
    oveq12d
    eqtrd
end
