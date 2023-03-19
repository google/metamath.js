include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "simp1.mm"
include "simp21r.mm"
include "simp22.mm"
include "simp23.mm"
include "simp31.mm"
include "simp33.mm"
include "cdlemg17b.mm"
include "syl123anc.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "simp21l.mm"
include "cdlemg17bq.mm"
include "syl133anc.mm"
include "oveq12d.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp32.mm"
include "cdlemg11aq.mm"
include "eqnetrrd.mm"
include "cdlemg17irq.mm"
include "eqid.mm"
include "cdlemg18c.mm"
include "eqeltrd.mm"

theorem cdlemg18d
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
  let vr: setvar r
  let cS: class S
  assume cdlemg12.l: |- .<_ = ( le ` K )
  assume cdlemg12.j: |- .\/ = ( join ` K )
  assume cdlemg12.m: |- ./\ = ( meet ` K )
  assume cdlemg12.a: |- A = ( Atoms ` K )
  assume cdlemg12.h: |- H = ( LHyp ` K )
  assume cdlemg12.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg12b.r: |- R = ( ( trL ` K ) ` W )

  disjoint A r
  disjoint G r
  disjoint .\/ r
  disjoint .<_ r
  disjoint P r
  disjoint Q r
  disjoint W r
  disjoint F r
  disjoint S r
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( F e. T /\ G e. T ) /\ P =/= Q /\ ( G ` P ) =/= P ) /\ ( ( R ` G ) .<_ ( P .\/ Q ) /\ ( ( F ` ( G ` P ) ) .\/ ( F ` ( G ` Q ) ) ) =/= ( P .\/ Q ) /\ -. E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ ( Q .\/ ( F ` ( G ` Q ) ) ) ) e. A )

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
    w3a
    #
    cF
    cT
    wcel
    #
    cG
    cT
    wcel
    #
    wa
    #
    cP
    cQ
    wne
    #
    cP
    cG
    cfv
    #
    cP
    wne
    #
    w3a
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
    #
    @8
    cF
    cfv
    #
    cQ
    cG
    cfv
    #
    cF
    cfv
    #
    c.or
    co
    #
    @11
    wne
    #
    vr
    cv
    #
    cW
    c.le
    wbr
    wn
    cP
    @18
    c.or
    co
    cQ
    @18
    c.or
    co
    wceq
    wa
    vr
    cA
    wrex
    wn
    #
    w3a
    #
    w3a
    #
    cP
    @13
    c.or
    co
    #
    cQ
    @15
    c.or
    co
    #
    c.an
    co
    cP
    cQ
    cF
    cfv
    #
    c.or
    co
    #
    cQ
    cP
    cF
    cfv
    #
    c.or
    co
    #
    c.an
    co
    #
    cA
    @21
    @22
    @25
    @23
    @27
    c.an
    @21
    @13
    @24
    cP
    c.or
    @21
    @8
    cQ
    cF
    @21
    @3
    @5
    @7
    @9
    @12
    @19
    @8
    cQ
    wceq
    @3
    @10
    @20
    simp1
    #
    @4
    @5
    @7
    @9
    @3
    @20
    simp21r
    #
    @3
    @6
    @7
    @9
    @20
    simp22
    #
    @3
    @6
    @7
    @9
    @20
    simp23
    #
    @3
    @10
    @12
    @17
    @19
    simp31
    #
    @3
    @10
    @12
    @17
    @19
    simp33
    #
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
    vr
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg17b
    syl123anc
    fveq2d
    #
    oveq2d
    @21
    @15
    @26
    cQ
    c.or
    @21
    @14
    cP
    cF
    @21
    @3
    @4
    @5
    @7
    @9
    @12
    @19
    @14
    cP
    wceq
    @29
    @4
    @5
    @7
    @9
    @3
    @20
    simp21l
    #
    @30
    @31
    @32
    @33
    @34
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
    cW
    vr
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg17bq
    syl133anc
    fveq2d
    #
    oveq2d
    oveq12d
    @21
    @0
    @1
    @2
    @4
    @7
    @26
    cQ
    wne
    @24
    @26
    c.or
    co
    #
    @11
    wne
    @28
    cA
    wcel
    @0
    @1
    @2
    @10
    @20
    simp11
    #
    @0
    @1
    @2
    @10
    @20
    simp12
    #
    @0
    @1
    @2
    @10
    @20
    simp13
    #
    @36
    @31
    @21
    @15
    @26
    cQ
    @37
    @21
    @0
    @1
    @2
    @4
    @5
    @17
    @15
    cQ
    wne
    @39
    @40
    @41
    @36
    @30
    @3
    @10
    @12
    @17
    @19
    simp32
    #
    cA
    cP
    cQ
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
    cdlemg11aq
    syl123anc
    eqnetrrd
    @21
    @16
    @38
    @11
    @21
    @13
    @24
    @15
    @26
    c.or
    @35
    @21
    @3
    @4
    @5
    @7
    @9
    @12
    @19
    @15
    @26
    wceq
    @29
    @36
    @30
    @31
    @32
    @33
    @34
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
    cW
    vr
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg17irq
    syl133anc
    oveq12d
    @42
    eqnetrrd
    cA
    cP
    cQ
    cR
    cT
    @11
    cW
    c.an
    co
    #
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
    @43
    eqid
    cdlemg18c
    syl133anc
    eqeltrd
end
