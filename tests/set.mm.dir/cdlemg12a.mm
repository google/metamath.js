include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "simp1l.mm"
include "simp21l.mm"
include "simp1.mm"
include "simp31.mm"
include "ltrnat.mm"
include "syl3anc.mm"
include "simp1r.mm"
include "simp21.mm"
include "simp22l.mm"
include "simp32.mm"
include "cdleme0a.mm"
include "syl212anc.mm"
include "simp33.mm"
include "2llnma3r.mm"
include "syl131anc.mm"
include "simp23.mm"
include "ltrncoat.mm"
include "syl121anc.mm"
include "hlatlej2.mm"
include "eqbrtrd.mm"

theorem cdlemg12a
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cU: class U
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
  assume cdlemg12.u: |- U = ( ( P .\/ Q ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ F e. T ) /\ ( G e. T /\ P =/= Q /\ ( P .\/ U ) =/= ( ( G ` P ) .\/ U ) ) ) -> ( ( P .\/ U ) ./\ ( ( G ` P ) .\/ U ) ) .<_ ( ( F ` ( G ` P ) ) .\/ U ) )

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
    cG
    cT
    wcel
    #
    cP
    cQ
    wne
    #
    cP
    cU
    c.or
    co
    #
    cP
    cG
    cfv
    #
    cU
    c.or
    co
    #
    wne
    #
    w3a
    #
    w3a
    #
    @13
    @15
    c.an
    co
    #
    cU
    @14
    cF
    cfv
    #
    cU
    c.or
    co
    #
    c.le
    @18
    @0
    @3
    @14
    cA
    wcel
    #
    cU
    cA
    wcel
    #
    @16
    @19
    cU
    wceq
    @0
    @1
    @10
    @17
    simp1l
    #
    @3
    @4
    @8
    @9
    @2
    @17
    simp21l
    #
    @18
    @2
    @11
    @3
    @22
    @2
    @10
    @17
    simp1
    #
    @2
    @10
    @11
    @12
    @16
    simp31
    #
    @25
    cA
    cP
    cT
    cG
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
    @18
    @0
    @1
    @5
    @6
    @12
    @23
    @24
    @0
    @1
    @10
    @17
    simp1r
    @2
    @5
    @8
    @9
    @17
    simp21
    @6
    @7
    @5
    @9
    @2
    @17
    simp22l
    @2
    @10
    @11
    @12
    @16
    simp32
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
    cdlemg12.u
    cdleme0a
    syl212anc
    #
    @2
    @10
    @11
    @12
    @16
    simp33
    cA
    cP
    @14
    cU
    c.or
    cK
    c.le
    c.an
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    2llnma3r
    syl131anc
    @18
    @0
    @20
    cA
    wcel
    #
    @23
    cU
    @21
    c.le
    wbr
    @24
    @18
    @2
    @9
    @11
    @3
    @29
    @26
    @2
    @5
    @8
    @9
    @17
    simp23
    @27
    @25
    cA
    cP
    cT
    cF
    cG
    cH
    cK
    c.le
    cW
    cdlemg12.l
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    ltrncoat
    syl121anc
    @28
    cA
    @20
    cU
    c.or
    cK
    c.le
    cdlemg12.l
    cdlemg12.j
    cdlemg12.a
    hlatlej2
    syl3anc
    eqbrtrd
end
