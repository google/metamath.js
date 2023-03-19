include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "simp33.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl21.mm"
include "simpl22.mm"
include "simpl23.mm"
include "simpl31.mm"
include "simpl32.mm"
include "cdlemg12d.mm"
include "syl123anc.mm"
include "simpr.mm"
include "oveq2d.mm"
include "col.mm"
include "cbs.mm"
include "simp11l.mm"
include "adantr.mm"
include "hlol.mm"
include "syl.mm"
include "simpl11.mm"
include "eqid.mm"
include "trlcl.mm"
include "syl2anc.mm"
include "olj01.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "cal.mm"
include "wb.mm"
include "hlatl.mm"
include "cops.mm"
include "hlop.mm"
include "simp12l.mm"
include "simp13l.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "opnlen0.mm"
include "syl31anc.mm"
include "simp11r.mm"
include "trlatn0.mm"
include "syl21anc.mm"
include "mpbird.mm"
include "atcmp.mm"
include "mpbid.mm"
include "eqcomd.mm"
include "ex.mm"
include "necon3d.mm"
include "mpd.mm"

theorem cdlemg12e
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
  let c.0: class .0.
  assume cdlemg12.l: |- .<_ = ( le ` K )
  assume cdlemg12.j: |- .\/ = ( join ` K )
  assume cdlemg12.m: |- ./\ = ( meet ` K )
  assume cdlemg12.a: |- A = ( Atoms ` K )
  assume cdlemg12.h: |- H = ( LHyp ` K )
  assume cdlemg12.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg12b.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemg12e.z: |- .0. = ( 0. ` K )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T /\ P =/= Q ) /\ ( -. ( R ` F ) .<_ ( P .\/ Q ) /\ -. ( R ` G ) .<_ ( P .\/ Q ) /\ ( R ` F ) =/= ( R ` G ) ) ) -> ( ( ( F ` ( G ` P ) ) .\/ P ) ./\ ( ( F ` ( G ` Q ) ) .\/ Q ) ) =/= .0. )

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
    cP
    cQ
    wne
    #
    w3a
    #
    cF
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
    wn
    #
    cG
    cR
    cfv
    #
    @15
    c.le
    wbr
    wn
    #
    @14
    @17
    wne
    #
    w3a
    #
    w3a
    #
    @19
    cP
    cG
    cfv
    cF
    cfv
    cP
    c.or
    co
    cQ
    cG
    cfv
    cF
    cfv
    cQ
    c.or
    co
    c.an
    co
    #
    c.0
    wne
    @9
    @13
    @16
    @18
    @19
    simp33
    @21
    @22
    c.0
    @14
    @17
    @21
    @22
    c.0
    wceq
    #
    @14
    @17
    wceq
    @21
    @23
    wa
    #
    @17
    @14
    @24
    @17
    @14
    c.le
    wbr
    #
    @17
    @14
    wceq
    #
    @24
    @17
    @14
    @22
    c.or
    co
    #
    @14
    c.le
    @24
    @9
    @10
    @11
    @12
    @16
    @18
    @17
    @27
    c.le
    wbr
    @9
    @13
    @20
    @23
    simpl1
    @10
    @11
    @12
    @9
    @20
    @23
    simpl21
    #
    @10
    @11
    @12
    @9
    @20
    @23
    simpl22
    #
    @10
    @11
    @12
    @9
    @20
    @23
    simpl23
    @16
    @18
    @19
    @9
    @13
    @23
    simpl31
    #
    @16
    @18
    @19
    @9
    @13
    @23
    simpl32
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
    cdlemg12d
    syl123anc
    @24
    @27
    @14
    c.0
    c.or
    co
    #
    @14
    @24
    @22
    c.0
    @14
    c.or
    @21
    @23
    simpr
    oveq2d
    @24
    cK
    col
    wcel
    #
    @14
    cK
    cbs
    cfv
    #
    wcel
    #
    @32
    @14
    wceq
    @24
    @0
    @33
    @21
    @0
    @23
    @0
    @1
    @5
    @8
    @13
    @20
    simp11l
    adantr
    #
    cK
    hlol
    syl
    @24
    @2
    @10
    @35
    @2
    @5
    @8
    @13
    @20
    @23
    simpl11
    #
    @28
    @34
    cR
    cT
    cF
    cH
    cK
    cW
    @34
    eqid
    #
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    trlcl
    syl2anc
    #
    @34
    c.or
    cK
    @14
    c.0
    @38
    cdlemg12.j
    cdlemg12e.z
    olj01
    syl2anc
    eqtrd
    breqtrd
    @24
    cK
    cal
    wcel
    #
    @17
    cA
    wcel
    #
    @14
    cA
    wcel
    #
    @25
    @26
    wb
    @24
    @0
    @40
    @36
    cK
    hlatl
    syl
    @24
    @41
    @17
    c.0
    wne
    #
    @24
    cK
    cops
    wcel
    #
    @17
    @34
    wcel
    #
    @15
    @34
    wcel
    #
    @18
    @43
    @24
    @0
    @44
    @36
    cK
    hlop
    syl
    #
    @24
    @2
    @11
    @45
    @37
    @29
    @34
    cR
    cT
    cG
    cH
    cK
    cW
    @38
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    trlcl
    syl2anc
    @24
    @0
    @3
    @6
    @46
    @36
    @21
    @3
    @23
    @3
    @4
    @2
    @8
    @13
    @20
    simp12l
    adantr
    @21
    @6
    @23
    @6
    @7
    @2
    @5
    @13
    @20
    simp13l
    adantr
    cA
    @34
    c.or
    cK
    cP
    cQ
    @38
    cdlemg12.j
    cdlemg12.a
    hlatjcl
    syl3anc
    #
    @31
    @34
    cK
    c.le
    @17
    @15
    c.0
    @38
    cdlemg12.l
    cdlemg12e.z
    opnlen0
    syl31anc
    @24
    @0
    @1
    @11
    @41
    @43
    wb
    @36
    @21
    @1
    @23
    @0
    @1
    @5
    @8
    @13
    @20
    simp11r
    adantr
    #
    @29
    cA
    cR
    cT
    cG
    cH
    cK
    cW
    c.0
    cdlemg12e.z
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    trlatn0
    syl21anc
    mpbird
    @24
    @42
    @14
    c.0
    wne
    #
    @24
    @44
    @35
    @46
    @16
    @50
    @47
    @39
    @48
    @30
    @34
    cK
    c.le
    @14
    @15
    c.0
    @38
    cdlemg12.l
    cdlemg12e.z
    opnlen0
    syl31anc
    @24
    @0
    @1
    @10
    @42
    @50
    wb
    @36
    @49
    @28
    cA
    cR
    cT
    cF
    cH
    cK
    cW
    c.0
    cdlemg12e.z
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    trlatn0
    syl21anc
    mpbird
    cA
    @17
    @14
    cK
    c.le
    cdlemg12.l
    cdlemg12.a
    atcmp
    syl3anc
    mpbid
    eqcomd
    ex
    necon3d
    mpd
end
