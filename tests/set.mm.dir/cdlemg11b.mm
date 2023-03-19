include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "w3a.mm"
include "simp33.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl31.mm"
include "simpl2l.mm"
include "trlval2.mm"
include "syl3anc.mm"
include "cbs.mm"
include "eqid.mm"
include "clat.mm"
include "simpl1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp2ll.mm"
include "adantr.mm"
include "atbase.mm"
include "ltrncl.mm"
include "latjcl.mm"
include "simpl1r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "simpl2r.mm"
include "latmle1.mm"
include "latlej1.mm"
include "simpr.mm"
include "breqtrrd.mm"
include "wb.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "lattrd.mm"
include "eqbrtrd.mm"
include "ex.mm"
include "necon3bd.mm"
include "mpd.mm"

theorem cdlemg11b
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
  assume cdlemg8.l: |- .<_ = ( le ` K )
  assume cdlemg8.j: |- .\/ = ( join ` K )
  assume cdlemg8.m: |- ./\ = ( meet ` K )
  assume cdlemg8.a: |- A = ( Atoms ` K )
  assume cdlemg8.h: |- H = ( LHyp ` K )
  assume cdlemg8.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg10.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ Q e. A ) /\ ( G e. T /\ P =/= Q /\ -. ( R ` G ) .<_ ( P .\/ Q ) ) ) -> ( P .\/ Q ) =/= ( ( G ` P ) .\/ ( G ` Q ) ) )

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
    wa
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
    #
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    w3a
    #
    w3a
    #
    @13
    @11
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
    #
    wne
    @2
    @7
    @8
    @9
    @13
    simp33
    @15
    @12
    @11
    @18
    @15
    @11
    @18
    wceq
    #
    @12
    @15
    @19
    wa
    #
    @10
    cP
    @16
    c.or
    co
    #
    cW
    c.an
    co
    #
    @11
    c.le
    @20
    @2
    @8
    @5
    @10
    @22
    wceq
    @2
    @7
    @14
    @19
    simpl1
    #
    @8
    @9
    @13
    @2
    @7
    @19
    simpl31
    #
    @5
    @6
    @2
    @14
    @19
    simpl2l
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
    cdlemg8.l
    cdlemg8.j
    cdlemg8.m
    cdlemg8.a
    cdlemg8.h
    cdlemg8.t
    cdlemg10.r
    trlval2
    syl3anc
    @20
    cK
    cbs
    cfv
    #
    cK
    c.le
    @22
    @21
    @11
    @25
    eqid
    #
    cdlemg8.l
    @20
    @0
    cK
    clat
    wcel
    #
    @0
    @1
    @7
    @14
    @19
    simpl1l
    cK
    hllat
    syl
    #
    @20
    @27
    @21
    @25
    wcel
    #
    cW
    @25
    wcel
    #
    @22
    @25
    wcel
    @28
    @20
    @27
    cP
    @25
    wcel
    #
    @16
    @25
    wcel
    #
    @29
    @28
    @20
    @3
    @31
    @15
    @3
    @19
    @3
    @4
    @6
    @2
    @14
    simp2ll
    adantr
    cA
    @25
    cP
    cK
    @26
    cdlemg8.a
    atbase
    syl
    #
    @20
    @2
    @8
    @31
    @32
    @23
    @24
    @33
    @25
    cT
    cG
    cH
    cK
    chlt
    cW
    cP
    @26
    cdlemg8.h
    cdlemg8.t
    ltrncl
    syl3anc
    #
    @25
    c.or
    cK
    cP
    @16
    @26
    cdlemg8.j
    latjcl
    syl3anc
    #
    @20
    @1
    @30
    @0
    @1
    @7
    @14
    @19
    simpl1r
    @25
    cH
    cK
    cW
    @26
    cdlemg8.h
    lhpbase
    syl
    #
    @25
    cK
    c.an
    @21
    cW
    @26
    cdlemg8.m
    latmcl
    syl3anc
    @35
    @20
    @27
    @31
    cQ
    @25
    wcel
    #
    @11
    @25
    wcel
    #
    @28
    @33
    @20
    @6
    @37
    @5
    @6
    @2
    @14
    @19
    simpl2r
    cA
    @25
    cQ
    cK
    @26
    cdlemg8.a
    atbase
    syl
    #
    @25
    c.or
    cK
    cP
    cQ
    @26
    cdlemg8.j
    latjcl
    syl3anc
    #
    @20
    @27
    @29
    @30
    @22
    @21
    c.le
    wbr
    @28
    @35
    @36
    @25
    cK
    c.le
    c.an
    @21
    cW
    @26
    cdlemg8.l
    cdlemg8.m
    latmle1
    syl3anc
    @20
    cP
    @11
    c.le
    wbr
    #
    @16
    @11
    c.le
    wbr
    #
    @21
    @11
    c.le
    wbr
    #
    @20
    @27
    @31
    @37
    @41
    @28
    @33
    @39
    @25
    c.or
    cK
    c.le
    cP
    cQ
    @26
    cdlemg8.l
    cdlemg8.j
    latlej1
    syl3anc
    @20
    @16
    @18
    @11
    c.le
    @20
    @27
    @32
    @17
    @25
    wcel
    #
    @16
    @18
    c.le
    wbr
    @28
    @34
    @20
    @2
    @8
    @37
    @44
    @23
    @24
    @39
    @25
    cT
    cG
    cH
    cK
    chlt
    cW
    cQ
    @26
    cdlemg8.h
    cdlemg8.t
    ltrncl
    syl3anc
    @25
    c.or
    cK
    c.le
    @16
    @17
    @26
    cdlemg8.l
    cdlemg8.j
    latlej1
    syl3anc
    @15
    @19
    simpr
    breqtrrd
    @20
    @27
    @31
    @32
    @38
    @41
    @42
    wa
    @43
    wb
    @28
    @33
    @34
    @40
    @25
    c.or
    cK
    c.le
    cP
    @16
    @11
    @26
    cdlemg8.l
    cdlemg8.j
    latjle12
    syl13anc
    mpbi2and
    lattrd
    eqbrtrd
    ex
    necon3bd
    mpd
end
