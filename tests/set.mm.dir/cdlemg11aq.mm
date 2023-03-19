include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "co.mm"
include "wne.mm"
include "w3a.mm"
include "simp1.mm"
include "simp2r.mm"
include "simp2l.mm"
include "simp31.mm"
include "simp32.mm"
include "simp33.mm"
include "wceq.mm"
include "simp1l.mm"
include "simp2ll.mm"
include "ltrncoat.mm"
include "syl121anc.mm"
include "simp2rl.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "3netr3d.mm"
include "cdlemg11a.mm"
include "syl123anc.mm"

theorem cdlemg11aq
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdlemg8.l: |- .<_ = ( le ` K )
  assume cdlemg8.j: |- .\/ = ( join ` K )
  assume cdlemg8.m: |- ./\ = ( meet ` K )
  assume cdlemg8.a: |- A = ( Atoms ` K )
  assume cdlemg8.h: |- H = ( LHyp ` K )
  assume cdlemg8.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T /\ ( ( F ` ( G ` P ) ) .\/ ( F ` ( G ` Q ) ) ) =/= ( P .\/ Q ) ) ) -> ( F ` ( G ` Q ) ) =/= Q )

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
    wa
    #
    cF
    cT
    wcel
    #
    cG
    cT
    wcel
    #
    cP
    cG
    cfv
    cF
    cfv
    #
    cQ
    cG
    cfv
    cF
    cfv
    #
    c.or
    co
    #
    cP
    cQ
    c.or
    co
    #
    wne
    #
    w3a
    #
    w3a
    #
    @2
    @8
    @5
    @10
    @11
    @13
    @12
    c.or
    co
    #
    cQ
    cP
    c.or
    co
    #
    wne
    @13
    cQ
    wne
    @2
    @9
    @17
    simp1
    #
    @2
    @5
    @8
    @17
    simp2r
    @2
    @5
    @8
    @17
    simp2l
    @2
    @9
    @10
    @11
    @16
    simp31
    #
    @2
    @9
    @10
    @11
    @16
    simp32
    #
    @18
    @14
    @15
    @19
    @20
    @2
    @9
    @10
    @11
    @16
    simp33
    @18
    @0
    @12
    cA
    wcel
    #
    @13
    cA
    wcel
    #
    @14
    @19
    wceq
    @0
    @1
    @9
    @17
    simp1l
    #
    @18
    @2
    @10
    @11
    @3
    @24
    @21
    @22
    @23
    @3
    @4
    @8
    @2
    @17
    simp2ll
    #
    cA
    cP
    cT
    cF
    cG
    cH
    cK
    c.le
    cW
    cdlemg8.l
    cdlemg8.a
    cdlemg8.h
    cdlemg8.t
    ltrncoat
    syl121anc
    @18
    @2
    @10
    @11
    @6
    @25
    @21
    @22
    @23
    @6
    @7
    @5
    @2
    @17
    simp2rl
    #
    cA
    cQ
    cT
    cF
    cG
    cH
    cK
    c.le
    cW
    cdlemg8.l
    cdlemg8.a
    cdlemg8.h
    cdlemg8.t
    ltrncoat
    syl121anc
    cA
    c.or
    cK
    @12
    @13
    cdlemg8.j
    cdlemg8.a
    hlatjcom
    syl3anc
    @18
    @0
    @3
    @6
    @15
    @20
    wceq
    @26
    @27
    @28
    cA
    c.or
    cK
    cP
    cQ
    cdlemg8.j
    cdlemg8.a
    hlatjcom
    syl3anc
    3netr3d
    cA
    cQ
    cP
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg8.l
    cdlemg8.j
    cdlemg8.m
    cdlemg8.a
    cdlemg8.h
    cdlemg8.t
    cdlemg11a
    syl123anc
end
