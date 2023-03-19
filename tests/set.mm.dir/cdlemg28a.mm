include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "w3a.mm"
include "cfv.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "simp11.mm"
include "simp12.mm"
include "simp21.mm"
include "simp22.mm"
include "simp23.mm"
include "simp1.mm"
include "simp21l.mm"
include "simp31l.mm"
include "simp32.mm"
include "simp33l.mm"
include "cdlemg27a.mm"
include "syl123anc.mm"
include "simp31r.mm"
include "simp33r.mm"
include "cdlemg25zz.mm"
include "syl133anc.mm"

theorem cdlemg28a
  let vz: setvar z
  let vv: setvar v
  let cA: class A
  let cP: class P
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
  let vr: setvar r
  let cQ: class Q
  let cS: class S
  assume cdlemg12.l: |- .<_ = ( le ` K )
  assume cdlemg12.j: |- .\/ = ( join ` K )
  assume cdlemg12.m: |- ./\ = ( meet ` K )
  assume cdlemg12.a: |- A = ( Atoms ` K )
  assume cdlemg12.h: |- H = ( LHyp ` K )
  assume cdlemg12.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg12b.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( v e. A /\ v .<_ W ) ) /\ ( ( z e. A /\ -. z .<_ W ) /\ F e. T /\ G e. T ) /\ ( ( v =/= ( R ` F ) /\ v =/= ( R ` G ) ) /\ z .<_ ( P .\/ v ) /\ ( ( F ` P ) =/= P /\ ( G ` P ) =/= P ) ) ) -> ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ W ) = ( ( z .\/ ( F ` ( G ` z ) ) ) ./\ W ) )

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
    vv
    cv
    #
    cA
    wcel
    @2
    cW
    c.le
    wbr
    wa
    #
    w3a
    #
    vz
    cv
    #
    cA
    wcel
    #
    @5
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
    cG
    cT
    wcel
    #
    w3a
    #
    @2
    cF
    cR
    cfv
    #
    wne
    #
    @2
    cG
    cR
    cfv
    #
    wne
    #
    wa
    #
    @5
    cP
    @2
    c.or
    co
    c.le
    wbr
    #
    cP
    cF
    cfv
    cP
    wne
    #
    cP
    cG
    cfv
    #
    cP
    wne
    #
    wa
    #
    w3a
    #
    w3a
    #
    @0
    @1
    @8
    @9
    @10
    @12
    cP
    @5
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    @14
    @24
    c.le
    wbr
    wn
    #
    cP
    @19
    cF
    cfv
    c.or
    co
    cW
    c.an
    co
    @5
    @5
    cG
    cfv
    cF
    cfv
    c.or
    co
    cW
    c.an
    co
    wceq
    @0
    @1
    @3
    @11
    @22
    simp11
    @0
    @1
    @3
    @11
    @22
    simp12
    @4
    @8
    @9
    @10
    @22
    simp21
    @4
    @8
    @9
    @10
    @22
    simp22
    #
    @4
    @8
    @9
    @10
    @22
    simp23
    #
    @23
    @4
    @6
    @9
    @13
    @17
    @18
    @25
    @4
    @11
    @22
    simp1
    #
    @6
    @7
    @9
    @10
    @4
    @22
    simp21l
    #
    @27
    @13
    @15
    @17
    @21
    @4
    @11
    simp31l
    @4
    @11
    @16
    @17
    @21
    simp32
    #
    @18
    @20
    @16
    @17
    @4
    @11
    simp33l
    vz
    vv
    cA
    cP
    cR
    cT
    cF
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
    cdlemg27a
    syl123anc
    @23
    @4
    @6
    @10
    @15
    @17
    @20
    @26
    @29
    @30
    @28
    @13
    @15
    @17
    @21
    @4
    @11
    simp31r
    @31
    @18
    @20
    @16
    @17
    @4
    @11
    simp33r
    vz
    vv
    cA
    cP
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
    cdlemg27a
    syl123anc
    vz
    cA
    cP
    cR
    cT
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
    cdlemg12b.r
    cdlemg25zz
    syl133anc
end
