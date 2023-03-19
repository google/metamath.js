include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "simp1.mm"
include "simp2.mm"
include "simp31.mm"
include "simp32.mm"
include "simp21.mm"
include "simp22l.mm"
include "simp33.mm"
include "cdlemg11b.mm"
include "syl123anc.mm"
include "wceq.mm"
include "simp1l.mm"
include "simp1r.mm"
include "eqid.mm"
include "cdlemg3a.mm"
include "syl211anc.mm"
include "simp22.mm"
include "cdlemg2k.mm"
include "syl121anc.mm"
include "3netr3d.mm"
include "cdlemg12a.mm"
include "syl113anc.mm"
include "oveq12d.mm"
include "simp23.mm"
include "cdlemg2l.mm"
include "syl122anc.mm"
include "3brtr4d.mm"

theorem cdlemg12b
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
  let cW: class W
  assume cdlemg12.l: |- .<_ = ( le ` K )
  assume cdlemg12.j: |- .\/ = ( join ` K )
  assume cdlemg12.m: |- ./\ = ( meet ` K )
  assume cdlemg12.a: |- A = ( Atoms ` K )
  assume cdlemg12.h: |- H = ( LHyp ` K )
  assume cdlemg12.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg12b.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ F e. T ) /\ ( G e. T /\ P =/= Q /\ -. ( R ` G ) .<_ ( P .\/ Q ) ) ) -> ( ( P .\/ Q ) ./\ ( ( G ` P ) .\/ ( G ` Q ) ) ) .<_ ( ( F ` ( G ` P ) ) .\/ ( F ` ( G ` Q ) ) ) )

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
    #
    cP
    cQ
    wne
    #
    cG
    cR
    cfv
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    w3a
    #
    w3a
    #
    cP
    @11
    cW
    c.an
    co
    #
    c.or
    co
    #
    cP
    cG
    cfv
    #
    @15
    c.or
    co
    #
    c.an
    co
    #
    @17
    cF
    cfv
    #
    @15
    c.or
    co
    #
    @11
    @17
    cQ
    cG
    cfv
    #
    c.or
    co
    #
    c.an
    co
    @20
    @22
    cF
    cfv
    c.or
    co
    #
    c.le
    @14
    @2
    @8
    @9
    @10
    @16
    @18
    wne
    @19
    @21
    c.le
    wbr
    @2
    @8
    @13
    simp1
    #
    @2
    @8
    @13
    simp2
    @2
    @8
    @9
    @10
    @12
    simp31
    #
    @2
    @8
    @9
    @10
    @12
    simp32
    #
    @14
    @11
    @23
    @16
    @18
    @14
    @2
    @3
    @4
    @9
    @10
    @12
    @11
    @23
    wne
    @25
    @2
    @3
    @6
    @7
    @13
    simp21
    #
    @4
    @5
    @3
    @7
    @2
    @13
    simp22l
    #
    @26
    @27
    @2
    @8
    @9
    @10
    @12
    simp33
    cA
    cP
    cQ
    cR
    cT
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg11b
    syl123anc
    @14
    @0
    @1
    @3
    @4
    @11
    @16
    wceq
    @0
    @1
    @8
    @13
    simp1l
    @0
    @1
    @8
    @13
    simp1r
    @28
    @29
    cA
    cP
    cQ
    @15
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    @15
    eqid
    #
    cdlemg3a
    syl211anc
    #
    @14
    @2
    @3
    @6
    @9
    @23
    @18
    wceq
    @25
    @28
    @2
    @3
    @6
    @7
    @13
    simp22
    #
    @26
    cA
    cP
    cQ
    cT
    @15
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg12.h
    cdlemg12.t
    cdlemg12.l
    cdlemg12.j
    cdlemg12.a
    cdlemg12.m
    @30
    cdlemg2k
    syl121anc
    #
    3netr3d
    cA
    cP
    cQ
    cT
    @15
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    @30
    cdlemg12a
    syl113anc
    @14
    @11
    @16
    @23
    @18
    c.an
    @31
    @33
    oveq12d
    @14
    @2
    @3
    @6
    @7
    @9
    @24
    @21
    wceq
    @25
    @28
    @32
    @2
    @3
    @6
    @7
    @13
    simp23
    @26
    cA
    cP
    cQ
    cT
    @15
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg12.h
    cdlemg12.t
    cdlemg12.l
    cdlemg12.j
    cdlemg12.a
    cdlemg12.m
    @30
    cdlemg2l
    syl122anc
    3brtr4d
end
