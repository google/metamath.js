include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wne.mm"
include "simp1.mm"
include "simp22.mm"
include "simp21.mm"
include "simp23.mm"
include "simp31.mm"
include "simp32.mm"
include "simp1l.mm"
include "ltrnel.mm"
include "syl3anc.mm"
include "simpld.mm"
include "hlatjcom.mm"
include "simp21l.mm"
include "simp22l.mm"
include "3eqtr3d.mm"
include "simp33.mm"
include "simpl1.mm"
include "simpl22.mm"
include "simpl21.mm"
include "simpl23.mm"
include "simpl31.mm"
include "simpr.mm"
include "cdlemg6.mm"
include "syl123anc.mm"
include "ex.mm"
include "necon3d.mm"
include "mpd.mm"
include "cdlemg8b.mm"
include "syl133anc.mm"
include "eqtr4d.mm"

theorem cdlemg8c
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ F e. T ) /\ ( G e. T /\ ( ( F ` ( G ` P ) ) .\/ ( F ` ( G ` Q ) ) ) = ( P .\/ Q ) /\ ( F ` ( G ` P ) ) =/= P ) ) -> ( Q .\/ ( F ` ( G ` Q ) ) ) = ( P .\/ Q ) )

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
    wceq
    #
    @13
    cP
    wne
    #
    w3a
    #
    w3a
    #
    cQ
    @15
    c.or
    co
    #
    cQ
    cP
    c.or
    co
    #
    @17
    @21
    @2
    @8
    @5
    @9
    @11
    @15
    @13
    c.or
    co
    #
    @23
    wceq
    @15
    cQ
    wne
    #
    @22
    @23
    wceq
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
    simp22
    #
    @2
    @5
    @8
    @9
    @20
    simp21
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
    @18
    @19
    simp31
    #
    @21
    @16
    @17
    @24
    @23
    @2
    @10
    @11
    @18
    @19
    simp32
    @21
    @0
    @13
    cA
    wcel
    #
    @15
    cA
    wcel
    #
    @16
    @24
    wceq
    @0
    @1
    @10
    @20
    simp1l
    #
    @21
    @2
    @9
    @12
    cA
    wcel
    @12
    cW
    c.le
    wbr
    wn
    wa
    #
    @31
    @26
    @29
    @21
    @2
    @11
    @5
    @34
    @26
    @30
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
    ltrnel
    syl3anc
    @2
    @9
    @34
    w3a
    @31
    @13
    cW
    c.le
    wbr
    wn
    cA
    @12
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemg8.l
    cdlemg8.a
    cdlemg8.h
    cdlemg8.t
    ltrnel
    simpld
    syl3anc
    @21
    @2
    @9
    @14
    cA
    wcel
    @14
    cW
    c.le
    wbr
    wn
    wa
    #
    @32
    @26
    @29
    @21
    @2
    @11
    @8
    @35
    @26
    @30
    @27
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
    ltrnel
    syl3anc
    @2
    @9
    @35
    w3a
    @32
    @15
    cW
    c.le
    wbr
    wn
    cA
    @14
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemg8.l
    cdlemg8.a
    cdlemg8.h
    cdlemg8.t
    ltrnel
    simpld
    syl3anc
    cA
    c.or
    cK
    @13
    @15
    cdlemg8.j
    cdlemg8.a
    hlatjcom
    syl3anc
    @21
    @0
    @3
    @6
    @17
    @23
    wceq
    @33
    @3
    @4
    @8
    @9
    @2
    @20
    simp21l
    @6
    @7
    @5
    @9
    @2
    @20
    simp22l
    cA
    c.or
    cK
    cP
    cQ
    cdlemg8.j
    cdlemg8.a
    hlatjcom
    syl3anc
    #
    3eqtr3d
    @21
    @19
    @25
    @2
    @10
    @11
    @18
    @19
    simp33
    @21
    @15
    cQ
    @13
    cP
    @21
    @15
    cQ
    wceq
    #
    @13
    cP
    wceq
    #
    @21
    @37
    wa
    @2
    @8
    @5
    @9
    @11
    @37
    @38
    @2
    @10
    @20
    @37
    simpl1
    @5
    @8
    @9
    @2
    @20
    @37
    simpl22
    @5
    @8
    @9
    @2
    @20
    @37
    simpl21
    @5
    @8
    @9
    @2
    @20
    @37
    simpl23
    @11
    @18
    @19
    @2
    @10
    @37
    simpl31
    @21
    @37
    simpr
    cA
    cQ
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
    cdlemg6
    syl123anc
    ex
    necon3d
    mpd
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
    cdlemg8b
    syl133anc
    @36
    eqtr4d
end
