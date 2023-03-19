include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wne.mm"
include "w3a.mm"
include "co.mm"
include "simp33.mm"
include "wceq.mm"
include "cmee.mm"
include "simpl1l.mm"
include "simp31l.mm"
include "adantr.mm"
include "simp1.mm"
include "simp2l.mm"
include "ltrnat.mm"
include "syl3anc.mm"
include "hlatlej1.mm"
include "simpr.mm"
include "clat.mm"
include "cbs.mm"
include "wb.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "atbase.mm"
include "simp2r.mm"
include "hlatjcl.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "simpl32.mm"
include "necomd.mm"
include "ps-1.mm"
include "syl132anc.mm"
include "mpbid.mm"
include "oveq1d.mm"
include "simpl1.mm"
include "simpl2r.mm"
include "simpl31.mm"
include "trlval2.mm"
include "simpl2l.mm"
include "3eqtr4rd.mm"
include "ex.mm"
include "necon3ad.mm"
include "mpd.mm"

theorem cdlemg42
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
  let cW: class W
  assume cdlemg42.l: |- .<_ = ( le ` K )
  assume cdlemg42.j: |- .\/ = ( join ` K )
  assume cdlemg42.a: |- A = ( Atoms ` K )
  assume cdlemg42.h: |- H = ( LHyp ` K )
  assume cdlemg42.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg42.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ G e. T ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( G ` P ) =/= P /\ ( R ` F ) =/= ( R ` G ) ) ) -> -. ( G ` P ) .<_ ( P .\/ ( F ` P ) ) )

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
    cP
    cG
    cfv
    #
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
    @13
    @9
    cP
    cP
    cF
    cfv
    #
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    @2
    @5
    @8
    @10
    @13
    simp33
    @15
    @18
    @11
    @12
    @15
    @18
    @11
    @12
    wceq
    @15
    @18
    wa
    #
    cP
    @9
    c.or
    co
    #
    cW
    cK
    cmee
    cfv
    #
    co
    #
    @17
    cW
    @21
    co
    #
    @12
    @11
    @19
    @20
    @17
    cW
    @21
    @19
    @20
    @17
    c.le
    wbr
    #
    @20
    @17
    wceq
    #
    @19
    cP
    @17
    c.le
    wbr
    #
    @18
    @24
    @19
    @0
    @6
    @16
    cA
    wcel
    #
    @26
    @0
    @1
    @5
    @14
    @18
    simpl1l
    #
    @15
    @6
    @18
    @6
    @7
    @10
    @13
    @2
    @5
    simp31l
    #
    adantr
    #
    @15
    @27
    @18
    @15
    @2
    @3
    @6
    @27
    @2
    @5
    @14
    simp1
    #
    @2
    @3
    @4
    @14
    simp2l
    @29
    cA
    cP
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemg42.l
    cdlemg42.a
    cdlemg42.h
    cdlemg42.t
    ltrnat
    syl3anc
    adantr
    #
    cA
    cP
    @16
    c.or
    cK
    c.le
    cdlemg42.l
    cdlemg42.j
    cdlemg42.a
    hlatlej1
    syl3anc
    @15
    @18
    simpr
    @19
    cK
    clat
    wcel
    #
    cP
    cK
    cbs
    cfv
    #
    wcel
    #
    @9
    @34
    wcel
    #
    @17
    @34
    wcel
    #
    @26
    @18
    wa
    @24
    wb
    @19
    @0
    @33
    @28
    cK
    hllat
    syl
    @19
    @6
    @35
    @30
    cA
    @34
    cP
    cK
    @34
    eqid
    #
    cdlemg42.a
    atbase
    syl
    @19
    @9
    cA
    wcel
    #
    @36
    @15
    @39
    @18
    @15
    @2
    @4
    @6
    @39
    @31
    @2
    @3
    @4
    @14
    simp2r
    @29
    cA
    cP
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemg42.l
    cdlemg42.a
    cdlemg42.h
    cdlemg42.t
    ltrnat
    syl3anc
    adantr
    #
    cA
    @34
    @9
    cK
    @38
    cdlemg42.a
    atbase
    syl
    @19
    @0
    @6
    @27
    @37
    @28
    @30
    @32
    cA
    @34
    c.or
    cK
    cP
    @16
    @38
    cdlemg42.j
    cdlemg42.a
    hlatjcl
    syl3anc
    @34
    c.or
    cK
    c.le
    cP
    @9
    @17
    @38
    cdlemg42.l
    cdlemg42.j
    latjle12
    syl13anc
    mpbi2and
    @19
    @0
    @6
    @39
    cP
    @9
    wne
    @6
    @27
    @24
    @25
    wb
    @28
    @30
    @40
    @19
    @9
    cP
    @8
    @10
    @13
    @2
    @5
    @18
    simpl32
    necomd
    @30
    @32
    cA
    cP
    @9
    cP
    @16
    c.or
    cK
    c.le
    cdlemg42.l
    cdlemg42.j
    cdlemg42.a
    ps-1
    syl132anc
    mpbid
    oveq1d
    @19
    @2
    @4
    @8
    @12
    @22
    wceq
    @2
    @5
    @14
    @18
    simpl1
    #
    @3
    @4
    @2
    @14
    @18
    simpl2r
    @8
    @10
    @13
    @2
    @5
    @18
    simpl31
    #
    cA
    cP
    cR
    cT
    cG
    cH
    c.or
    cK
    c.le
    @21
    cW
    cdlemg42.l
    cdlemg42.j
    @21
    eqid
    #
    cdlemg42.a
    cdlemg42.h
    cdlemg42.t
    cdlemg42.r
    trlval2
    syl3anc
    @19
    @2
    @3
    @8
    @11
    @23
    wceq
    @41
    @3
    @4
    @2
    @14
    @18
    simpl2l
    @42
    cA
    cP
    cR
    cT
    cF
    cH
    c.or
    cK
    c.le
    @21
    cW
    cdlemg42.l
    cdlemg42.j
    @43
    cdlemg42.a
    cdlemg42.h
    cdlemg42.t
    cdlemg42.r
    trlval2
    syl3anc
    3eqtr4rd
    ex
    necon3ad
    mpd
end
