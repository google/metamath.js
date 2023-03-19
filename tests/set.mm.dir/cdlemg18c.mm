include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "simp1l.mm"
include "simp21l.mm"
include "simp1r.mm"
include "simp21.mm"
include "simp22l.mm"
include "simp31.mm"
include "cdleme0a.mm"
include "syl212anc.mm"
include "simp1.mm"
include "simp23.mm"
include "ltrnat.mm"
include "syl3anc.mm"
include "cdlemg18b.mm"
include "simp32.mm"
include "necomd.mm"
include "jca.mm"
include "simp33.mm"
include "cdlemg18a.mm"
include "syl132anc.mm"
include "hlatlej2.mm"
include "wceq.mm"
include "cdleme0cp.mm"
include "syl22anc.mm"
include "breqtrrd.mm"
include "simp22.mm"
include "cdlemg2kq.mm"
include "syl121anc.mm"
include "hlatjcom.mm"
include "3eqtr3d.mm"
include "breqtrd.mm"
include "ps-2c.mm"
include "syl333anc.mm"

theorem cdlemg18c
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cU: class U
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let vr: setvar r
  let cG: class G
  let cS: class S
  assume cdlemg12.l: |- .<_ = ( le ` K )
  assume cdlemg12.j: |- .\/ = ( join ` K )
  assume cdlemg12.m: |- ./\ = ( meet ` K )
  assume cdlemg12.a: |- A = ( Atoms ` K )
  assume cdlemg12.h: |- H = ( LHyp ` K )
  assume cdlemg12.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg12b.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemg18b.u: |- U = ( ( P .\/ Q ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ F e. T ) /\ ( P =/= Q /\ ( F ` P ) =/= Q /\ ( ( F ` Q ) .\/ ( F ` P ) ) =/= ( P .\/ Q ) ) ) -> ( ( P .\/ ( F ` Q ) ) ./\ ( Q .\/ ( F ` P ) ) ) e. A )

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
    cF
    cT
    wcel
    #
    w3a
    #
    cP
    cQ
    wne
    #
    cP
    cF
    cfv
    #
    cQ
    wne
    #
    cQ
    cF
    cfv
    #
    @12
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
    @0
    @3
    cU
    cA
    wcel
    #
    @14
    cA
    wcel
    #
    @6
    @12
    cA
    wcel
    #
    cP
    cU
    @14
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    cQ
    @12
    wne
    #
    wa
    cP
    @14
    c.or
    co
    #
    cQ
    @12
    c.or
    co
    #
    wne
    #
    cQ
    cP
    cU
    c.or
    co
    #
    c.le
    wbr
    #
    @12
    @23
    c.le
    wbr
    #
    wa
    @26
    @27
    c.an
    co
    cA
    wcel
    @0
    @1
    @10
    @18
    simp1l
    #
    @3
    @4
    @8
    @9
    @2
    @18
    simp21l
    #
    @19
    @0
    @1
    @5
    @6
    @11
    @20
    @32
    @0
    @1
    @10
    @18
    simp1r
    #
    @2
    @5
    @8
    @9
    @18
    simp21
    #
    @6
    @7
    @5
    @9
    @2
    @18
    simp22l
    #
    @2
    @10
    @11
    @13
    @17
    simp31
    #
    cA
    cP
    cQ
    cU
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
    cdlemg18b.u
    cdleme0a
    syl212anc
    #
    @19
    @2
    @9
    @6
    @21
    @2
    @10
    @18
    simp1
    #
    @2
    @5
    @8
    @9
    @18
    simp23
    #
    @36
    cA
    cQ
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemg12.l
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    ltrnat
    syl3anc
    #
    @36
    @19
    @2
    @9
    @3
    @22
    @39
    @40
    @33
    cA
    cP
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemg12.l
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    ltrnat
    syl3anc
    #
    @19
    @24
    @25
    cA
    cP
    cQ
    cR
    cT
    cU
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
    cdlemg18b.u
    cdlemg18b
    @19
    @12
    cQ
    @2
    @10
    @11
    @13
    @17
    simp32
    necomd
    jca
    @19
    @2
    @3
    @6
    @9
    @11
    @17
    @28
    @39
    @33
    @36
    @40
    @37
    @2
    @10
    @11
    @13
    @17
    simp33
    cA
    cP
    cQ
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
    cdlemg18a
    syl132anc
    @19
    @30
    @31
    @19
    cQ
    @16
    @29
    c.le
    @19
    @0
    @3
    @6
    cQ
    @16
    c.le
    wbr
    @32
    @33
    @36
    cA
    cP
    cQ
    c.or
    cK
    c.le
    cdlemg12.l
    cdlemg12.j
    cdlemg12.a
    hlatlej2
    syl3anc
    @19
    @0
    @1
    @5
    @6
    @29
    @16
    wceq
    @32
    @34
    @35
    @36
    cA
    cP
    cQ
    cU
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
    cdlemg18b.u
    cdleme0cp
    syl22anc
    breqtrrd
    @19
    @12
    @15
    @23
    c.le
    @19
    @0
    @21
    @22
    @12
    @15
    c.le
    wbr
    @32
    @41
    @42
    cA
    @14
    @12
    c.or
    cK
    c.le
    cdlemg12.l
    cdlemg12.j
    cdlemg12.a
    hlatlej2
    syl3anc
    @19
    @12
    @14
    c.or
    co
    #
    @14
    cU
    c.or
    co
    #
    @15
    @23
    @19
    @2
    @5
    @8
    @9
    @43
    @44
    wceq
    @39
    @35
    @2
    @5
    @8
    @9
    @18
    simp22
    @40
    cA
    cP
    cQ
    cT
    cU
    cF
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
    cdlemg18b.u
    cdlemg2kq
    syl121anc
    @19
    @0
    @22
    @21
    @43
    @15
    wceq
    @32
    @42
    @41
    cA
    c.or
    cK
    @12
    @14
    cdlemg12.j
    cdlemg12.a
    hlatjcom
    syl3anc
    @19
    @0
    @21
    @20
    @44
    @23
    wceq
    @32
    @41
    @38
    cA
    c.or
    cK
    @14
    cU
    cdlemg12.j
    cdlemg12.a
    hlatjcom
    syl3anc
    3eqtr3d
    breqtrd
    jca
    cA
    cP
    cU
    @14
    cQ
    @12
    c.or
    cK
    c.le
    c.an
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    ps-2c
    syl333anc
end
