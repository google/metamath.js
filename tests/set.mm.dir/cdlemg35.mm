include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wrex.mm"
include "simp1l.mm"
include "simp1.mm"
include "simp21.mm"
include "simp22.mm"
include "simp31.mm"
include "trlat.mm"
include "syl112anc.mm"
include "simp23.mm"
include "simp32.mm"
include "simp33.mm"
include "hlsupr.mm"
include "syl31anc.mm"
include "cbs.mm"
include "eqid.mm"
include "clat.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "atbase.mm"
include "3ad2ant2.mm"
include "simp11.mm"
include "simp122.mm"
include "trlcl.mm"
include "syl2anc.mm"
include "simp123.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "trlle.mm"
include "wb.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "lattrd.mm"
include "jca32.mm"
include "3expia.mm"
include "reximdva.mm"
include "mpd.mm"

theorem cdlemg35
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
  assume cdlemg35.l: |- .<_ = ( le ` K )
  assume cdlemg35.j: |- .\/ = ( join ` K )
  assume cdlemg35.m: |- ./\ = ( meet ` K )
  assume cdlemg35.a: |- A = ( Atoms ` K )
  assume cdlemg35.h: |- H = ( LHyp ` K )
  assume cdlemg35.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg35.r: |- R = ( ( trL ` K ) ` W )

  disjoint A v
  disjoint F v
  disjoint G v
  disjoint H v
  disjoint K v
  disjoint .<_ v
  disjoint P v
  disjoint R v
  disjoint T v
  disjoint W v
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ F e. T /\ G e. T ) /\ ( ( F ` P ) =/= P /\ ( G ` P ) =/= P /\ ( R ` F ) =/= ( R ` G ) ) ) -> E. v e. A ( v .<_ W /\ ( v =/= ( R ` F ) /\ v =/= ( R ` G ) ) ) )

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
    cP
    cF
    cfv
    cP
    wne
    #
    cP
    cG
    cfv
    cP
    wne
    #
    cF
    cR
    cfv
    #
    cG
    cR
    cfv
    #
    wne
    #
    w3a
    #
    w3a
    #
    vv
    cv
    #
    @9
    wne
    #
    @14
    @10
    wne
    #
    @14
    @9
    @10
    c.or
    co
    #
    c.le
    wbr
    #
    w3a
    #
    vv
    cA
    wrex
    #
    @14
    cW
    c.le
    wbr
    #
    @15
    @16
    wa
    wa
    #
    vv
    cA
    wrex
    @13
    @0
    @9
    cA
    wcel
    #
    @10
    cA
    wcel
    #
    @11
    @20
    @0
    @1
    @6
    @12
    simp1l
    @13
    @2
    @3
    @4
    @7
    @23
    @2
    @6
    @12
    simp1
    #
    @2
    @3
    @4
    @5
    @12
    simp21
    #
    @2
    @3
    @4
    @5
    @12
    simp22
    @2
    @6
    @7
    @8
    @11
    simp31
    cA
    cP
    cR
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemg35.l
    cdlemg35.a
    cdlemg35.h
    cdlemg35.t
    cdlemg35.r
    trlat
    syl112anc
    @13
    @2
    @3
    @5
    @8
    @24
    @25
    @26
    @2
    @3
    @4
    @5
    @12
    simp23
    @2
    @6
    @7
    @8
    @11
    simp32
    cA
    cP
    cR
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemg35.l
    cdlemg35.a
    cdlemg35.h
    cdlemg35.t
    cdlemg35.r
    trlat
    syl112anc
    @2
    @6
    @7
    @8
    @11
    simp33
    cA
    @9
    @10
    c.or
    cK
    c.le
    vv
    cdlemg35.l
    cdlemg35.j
    cdlemg35.a
    hlsupr
    syl31anc
    @13
    @19
    @22
    vv
    cA
    @13
    @14
    cA
    wcel
    #
    @19
    @22
    @13
    @27
    @19
    w3a
    #
    @21
    @15
    @16
    @28
    cK
    cbs
    cfv
    #
    cK
    c.le
    @14
    @17
    cW
    @29
    eqid
    #
    cdlemg35.l
    @28
    @0
    cK
    clat
    wcel
    #
    @0
    @1
    @6
    @12
    @27
    @19
    simp11l
    cK
    hllat
    syl
    #
    @27
    @13
    @14
    @29
    wcel
    @19
    cA
    @29
    @14
    cK
    @30
    cdlemg35.a
    atbase
    3ad2ant2
    @28
    @31
    @9
    @29
    wcel
    #
    @10
    @29
    wcel
    #
    @17
    @29
    wcel
    @32
    @28
    @2
    @4
    @33
    @2
    @6
    @12
    @27
    @19
    simp11
    #
    @3
    @4
    @5
    @2
    @12
    @27
    @19
    simp122
    #
    @29
    cR
    cT
    cF
    cH
    cK
    cW
    @30
    cdlemg35.h
    cdlemg35.t
    cdlemg35.r
    trlcl
    syl2anc
    #
    @28
    @2
    @5
    @34
    @35
    @3
    @4
    @5
    @2
    @12
    @27
    @19
    simp123
    #
    @29
    cR
    cT
    cG
    cH
    cK
    cW
    @30
    cdlemg35.h
    cdlemg35.t
    cdlemg35.r
    trlcl
    syl2anc
    #
    @29
    c.or
    cK
    @9
    @10
    @30
    cdlemg35.j
    latjcl
    syl3anc
    @28
    @1
    cW
    @29
    wcel
    #
    @0
    @1
    @6
    @12
    @27
    @19
    simp11r
    @29
    cH
    cK
    cW
    @30
    cdlemg35.h
    lhpbase
    syl
    #
    @13
    @27
    @15
    @16
    @18
    simp33
    @28
    @9
    cW
    c.le
    wbr
    #
    @10
    cW
    c.le
    wbr
    #
    @17
    cW
    c.le
    wbr
    #
    @28
    @2
    @4
    @42
    @35
    @36
    cR
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemg35.l
    cdlemg35.h
    cdlemg35.t
    cdlemg35.r
    trlle
    syl2anc
    @28
    @2
    @5
    @43
    @35
    @38
    cR
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemg35.l
    cdlemg35.h
    cdlemg35.t
    cdlemg35.r
    trlle
    syl2anc
    @28
    @31
    @33
    @34
    @40
    @42
    @43
    wa
    @44
    wb
    @32
    @37
    @39
    @41
    @29
    c.or
    cK
    c.le
    @9
    @10
    cW
    @30
    cdlemg35.l
    cdlemg35.j
    latjle12
    syl13anc
    mpbi2and
    lattrd
    @13
    @27
    @15
    @16
    @18
    simp31
    @13
    @27
    @15
    @16
    @18
    simp32
    jca32
    3expia
    reximdva
    mpd
end
