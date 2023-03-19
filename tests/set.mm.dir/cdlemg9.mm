include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "cdlemg9b.mm"
include "wi.mm"
include "simp1l.mm"
include "simp21l.mm"
include "simp1.mm"
include "simp23.mm"
include "simp31.mm"
include "ltrncoat.mm"
include "syl121anc.mm"
include "ltrnat.mm"
include "syl3anc.mm"
include "simp22l.mm"
include "dalaw.mm"
include "syl133anc.mm"
include "mpd.mm"

theorem cdlemg9
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ F e. T ) /\ ( G e. T /\ P =/= Q /\ ( ( F ` ( G ` P ) ) .\/ ( F ` ( G ` Q ) ) ) =/= ( P .\/ Q ) ) ) -> ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ ( Q .\/ ( F ` ( G ` Q ) ) ) ) .<_ ( ( ( ( F ` ( G ` P ) ) .\/ ( G ` P ) ) ./\ ( ( F ` ( G ` Q ) ) .\/ ( G ` Q ) ) ) .\/ ( ( ( G ` P ) .\/ P ) ./\ ( ( G ` Q ) .\/ Q ) ) ) )

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
    cG
    cfv
    #
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
    @18
    @17
    c.an
    co
    @13
    @15
    c.or
    co
    c.le
    wbr
    #
    cP
    @14
    c.or
    co
    cQ
    @16
    c.or
    co
    c.an
    co
    @14
    @13
    c.or
    co
    @16
    @15
    c.or
    co
    c.an
    co
    @13
    cP
    c.or
    co
    @15
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
    cdlemg9b
    @21
    @0
    @3
    @14
    cA
    wcel
    #
    @13
    cA
    wcel
    #
    @6
    @16
    cA
    wcel
    #
    @15
    cA
    wcel
    #
    @22
    @23
    wi
    @0
    @1
    @10
    @20
    simp1l
    @3
    @4
    @8
    @9
    @2
    @20
    simp21l
    #
    @21
    @2
    @9
    @11
    @3
    @24
    @2
    @10
    @20
    simp1
    #
    @2
    @5
    @8
    @9
    @20
    simp23
    #
    @2
    @10
    @11
    @12
    @19
    simp31
    #
    @28
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
    @21
    @2
    @11
    @3
    @25
    @29
    @31
    @28
    cA
    cP
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemg8.l
    cdlemg8.a
    cdlemg8.h
    cdlemg8.t
    ltrnat
    syl3anc
    @6
    @7
    @5
    @9
    @2
    @20
    simp22l
    #
    @21
    @2
    @9
    @11
    @6
    @26
    @29
    @30
    @31
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
    cdlemg8.l
    cdlemg8.a
    cdlemg8.h
    cdlemg8.t
    ltrncoat
    syl121anc
    @21
    @2
    @11
    @6
    @27
    @29
    @31
    @32
    cA
    cQ
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemg8.l
    cdlemg8.a
    cdlemg8.h
    cdlemg8.t
    ltrnat
    syl3anc
    cA
    cP
    @14
    @13
    cQ
    @16
    @15
    c.or
    cK
    c.le
    c.an
    cdlemg8.l
    cdlemg8.j
    cdlemg8.m
    cdlemg8.a
    dalaw
    syl133anc
    mpd
end
