include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "simp3l.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "trlle.mm"
include "syl21anc.mm"
include "clat.mm"
include "cbs.mm"
include "wb.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "trlcl.mm"
include "simp21l.mm"
include "simp22.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "lhpbase.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "cal.mm"
include "hlatl.mm"
include "simp21.mm"
include "simp3r.mm"
include "trlat.mm"
include "syl212anc.mm"
include "simp23.mm"
include "lhpat.mm"
include "atcmp.mm"
include "mpbid.mm"

theorem cdlemg17dALTN
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let vr: setvar r
  assume cdlemg12.l: |- .<_ = ( le ` K )
  assume cdlemg12.j: |- .\/ = ( join ` K )
  assume cdlemg12.m: |- ./\ = ( meet ` K )
  assume cdlemg12.a: |- A = ( Atoms ` K )
  assume cdlemg12.h: |- H = ( LHyp ` K )
  assume cdlemg12.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg12b.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H /\ G e. T ) /\ ( ( P e. A /\ -. P .<_ W ) /\ Q e. A /\ P =/= Q ) /\ ( ( R ` G ) .<_ ( P .\/ Q ) /\ ( G ` P ) =/= P ) ) -> ( R ` G ) = ( ( P .\/ Q ) ./\ W ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    cG
    cT
    wcel
    #
    w3a
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
    cP
    cQ
    wne
    #
    w3a
    #
    cG
    cR
    cfv
    #
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    cP
    cG
    cfv
    cP
    wne
    #
    wa
    #
    w3a
    #
    @10
    @11
    cW
    c.an
    co
    #
    c.le
    wbr
    #
    @10
    @16
    wceq
    #
    @15
    @12
    @10
    cW
    c.le
    wbr
    #
    @17
    @3
    @9
    @12
    @13
    simp3l
    @15
    @0
    @1
    @2
    @19
    @0
    @1
    @2
    @9
    @14
    simp11
    #
    @0
    @1
    @2
    @9
    @14
    simp12
    #
    @0
    @1
    @2
    @9
    @14
    simp13
    #
    cR
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemg12.l
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    trlle
    syl21anc
    @15
    cK
    clat
    wcel
    #
    @10
    cK
    cbs
    cfv
    #
    wcel
    #
    @11
    @24
    wcel
    #
    cW
    @24
    wcel
    #
    @12
    @19
    wa
    @17
    wb
    @15
    @0
    @23
    @20
    cK
    hllat
    syl
    @15
    @0
    @1
    @2
    @25
    @20
    @21
    @22
    @24
    cR
    cT
    cG
    cH
    cK
    cW
    @24
    eqid
    #
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    trlcl
    syl21anc
    @15
    @0
    @4
    @7
    @26
    @20
    @4
    @5
    @7
    @8
    @3
    @14
    simp21l
    @3
    @6
    @7
    @8
    @14
    simp22
    #
    cA
    @24
    c.or
    cK
    cP
    cQ
    @28
    cdlemg12.j
    cdlemg12.a
    hlatjcl
    syl3anc
    @15
    @1
    @27
    @21
    @24
    cH
    cK
    cW
    @28
    cdlemg12.h
    lhpbase
    syl
    @24
    cK
    c.le
    c.an
    @10
    @11
    cW
    @28
    cdlemg12.l
    cdlemg12.m
    latlem12
    syl13anc
    mpbi2and
    @15
    cK
    cal
    wcel
    #
    @10
    cA
    wcel
    #
    @16
    cA
    wcel
    #
    @17
    @18
    wb
    @15
    @0
    @30
    @20
    cK
    hlatl
    syl
    @15
    @0
    @1
    @6
    @2
    @13
    @31
    @20
    @21
    @3
    @6
    @7
    @8
    @14
    simp21
    #
    @22
    @3
    @9
    @12
    @13
    simp3r
    cA
    cP
    cR
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
    cdlemg12b.r
    trlat
    syl212anc
    @15
    @0
    @1
    @6
    @7
    @8
    @32
    @20
    @21
    @33
    @29
    @3
    @6
    @7
    @8
    @14
    simp23
    cA
    cP
    cQ
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
    lhpat
    syl212anc
    cA
    @10
    @16
    cK
    c.le
    cdlemg12.l
    cdlemg12.a
    atcmp
    syl3anc
    mpbid
end
