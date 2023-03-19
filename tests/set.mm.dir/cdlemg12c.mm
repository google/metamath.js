include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "cdlemg12b.mm"
include "wi.mm"
include "simp1l.mm"
include "simp21l.mm"
include "simp1.mm"
include "simp31.mm"
include "ltrnat.mm"
include "syl3anc.mm"
include "simp23.mm"
include "simp22l.mm"
include "ltrncoat.mm"
include "syl121anc.mm"
include "dalaw.mm"
include "syl133anc.mm"
include "mpd.mm"

theorem cdlemg12c
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ F e. T ) /\ ( G e. T /\ P =/= Q /\ -. ( R ` G ) .<_ ( P .\/ Q ) ) ) -> ( ( P .\/ ( G ` P ) ) ./\ ( Q .\/ ( G ` Q ) ) ) .<_ ( ( ( ( G ` P ) .\/ ( F ` ( G ` P ) ) ) ./\ ( ( G ` Q ) .\/ ( F ` ( G ` Q ) ) ) ) .\/ ( ( ( F ` ( G ` P ) ) .\/ P ) ./\ ( ( F ` ( G ` Q ) ) .\/ Q ) ) ) )

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
    @13
    cP
    cG
    cfv
    #
    cQ
    cG
    cfv
    #
    c.or
    co
    c.an
    co
    @17
    cF
    cfv
    #
    @18
    cF
    cfv
    #
    c.or
    co
    c.le
    wbr
    #
    cP
    @17
    c.or
    co
    cQ
    @18
    c.or
    co
    c.an
    co
    @17
    @19
    c.or
    co
    @18
    @20
    c.or
    co
    c.an
    co
    @19
    cP
    c.or
    co
    @20
    cQ
    c.or
    co
    c.an
    co
    c.or
    co
    c.le
    wbr
    #
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
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg12b
    @16
    @0
    @3
    @17
    cA
    wcel
    #
    @19
    cA
    wcel
    #
    @6
    @18
    cA
    wcel
    #
    @20
    cA
    wcel
    #
    @21
    @22
    wi
    @0
    @1
    @10
    @15
    simp1l
    @3
    @4
    @8
    @9
    @2
    @15
    simp21l
    #
    @16
    @2
    @11
    @3
    @23
    @2
    @10
    @15
    simp1
    #
    @2
    @10
    @11
    @12
    @14
    simp31
    #
    @27
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
    #
    @16
    @2
    @9
    @23
    @24
    @28
    @2
    @5
    @8
    @9
    @15
    simp23
    #
    @30
    cA
    @17
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
    @6
    @7
    @5
    @9
    @2
    @15
    simp22l
    #
    @16
    @2
    @11
    @6
    @25
    @28
    @29
    @32
    cA
    cQ
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
    @16
    @2
    @9
    @11
    @6
    @26
    @28
    @31
    @29
    @32
    cA
    cQ
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
    cA
    cP
    @17
    @19
    cQ
    @18
    @20
    c.or
    cK
    c.le
    c.an
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    dalaw
    syl133anc
    mpd
end
