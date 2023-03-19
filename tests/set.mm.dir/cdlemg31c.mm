include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "wne.mm"
include "co.mm"
include "simp11l.mm"
include "simp11r.mm"
include "jca.mm"
include "simp13.mm"
include "simp31.mm"
include "necomd.mm"
include "simp12.mm"
include "simp2r.mm"
include "simp32.mm"
include "trlat.mm"
include "syl112anc.mm"
include "trlle.mm"
include "syl2anc.mm"
include "simp2l.mm"
include "lhp2atnle.mm"
include "syl321anc.mm"
include "wceq.mm"
include "simp12l.mm"
include "simp13l.mm"
include "simp2ll.mm"
include "cdlemg31a.mm"
include "syl222anc.mm"
include "adantr.mm"
include "simp111.mm"
include "simp112.mm"
include "simp3.mm"
include "simp133.mm"
include "simp2.mm"
include "syl312anc.mm"
include "3expia.mm"
include "necon4ad.mm"
include "mpd.mm"
include "cdlemg31b.mm"
include "eqbrtrrd.mm"
include "mtand.mm"

theorem cdlemg31c
  let vv: setvar v
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
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
  assume cdlemg31.n: |- N = ( ( P .\/ v ) ./\ ( Q .\/ ( R ` F ) ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( v e. A /\ v .<_ W ) /\ F e. T ) /\ ( v =/= ( R ` F ) /\ ( F ` P ) =/= P /\ N e. A ) ) -> -. N .<_ W )

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
    vv
    cv
    #
    cA
    wcel
    #
    @10
    cW
    c.le
    wbr
    #
    wa
    #
    cF
    cT
    wcel
    #
    wa
    #
    @10
    cF
    cR
    cfv
    #
    wne
    #
    cP
    cF
    cfv
    cP
    wne
    #
    cN
    cA
    wcel
    #
    w3a
    #
    w3a
    #
    cN
    cW
    c.le
    wbr
    #
    @10
    cQ
    @16
    c.or
    co
    #
    c.le
    wbr
    #
    @21
    @2
    @8
    @16
    @10
    wne
    @16
    cA
    wcel
    #
    @16
    cW
    c.le
    wbr
    #
    @13
    @24
    wn
    @21
    @0
    @1
    @0
    @1
    @5
    @8
    @15
    @20
    simp11l
    #
    @0
    @1
    @5
    @8
    @15
    @20
    simp11r
    #
    jca
    #
    @2
    @5
    @8
    @15
    @20
    simp13
    @21
    @10
    @16
    @9
    @15
    @17
    @18
    @19
    simp31
    necomd
    @21
    @2
    @5
    @14
    @18
    @25
    @29
    @2
    @5
    @8
    @15
    @20
    simp12
    @9
    @13
    @14
    @20
    simp2r
    #
    @9
    @15
    @17
    @18
    @19
    simp32
    cA
    cP
    cR
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
    cdlemg12b.r
    trlat
    syl112anc
    @21
    @2
    @14
    @26
    @29
    @30
    cR
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemg12.l
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    trlle
    syl2anc
    @9
    @13
    @14
    @20
    simp2l
    cA
    cQ
    @16
    cH
    c.or
    cK
    c.le
    @10
    cW
    cdlemg12.l
    cdlemg12.j
    cdlemg12.a
    cdlemg12.h
    lhp2atnle
    syl321anc
    @21
    @22
    wa
    #
    cN
    @10
    @23
    c.le
    @31
    cN
    cP
    @10
    c.or
    co
    c.le
    wbr
    #
    cN
    @10
    wceq
    @21
    @32
    @22
    @21
    @0
    @1
    @3
    @6
    @11
    @14
    @32
    @27
    @28
    @3
    @4
    @2
    @8
    @15
    @20
    simp12l
    #
    @6
    @7
    @2
    @5
    @15
    @20
    simp13l
    #
    @11
    @12
    @14
    @9
    @20
    simp2ll
    #
    @30
    vv
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
    cN
    cW
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg31.n
    cdlemg31a
    syl222anc
    adantr
    @31
    @32
    cN
    @10
    @21
    @22
    cN
    @10
    wne
    #
    @32
    wn
    #
    @21
    @22
    @36
    w3a
    #
    @2
    @5
    @10
    cN
    wne
    @13
    @19
    @22
    @37
    @2
    @5
    @8
    @15
    @20
    @22
    @36
    simp111
    @2
    @5
    @8
    @15
    @20
    @22
    @36
    simp112
    @38
    cN
    @10
    @21
    @22
    @36
    simp3
    necomd
    @13
    @14
    @9
    @20
    @22
    @36
    simp12l
    @17
    @18
    @19
    @9
    @15
    @22
    @36
    simp133
    @21
    @22
    @36
    simp2
    cA
    cP
    @10
    cH
    c.or
    cK
    c.le
    cN
    cW
    cdlemg12.l
    cdlemg12.j
    cdlemg12.a
    cdlemg12.h
    lhp2atnle
    syl312anc
    3expia
    necon4ad
    mpd
    @21
    cN
    @23
    c.le
    wbr
    #
    @22
    @21
    @0
    @1
    @3
    @6
    @11
    @14
    @39
    @27
    @28
    @33
    @34
    @35
    @30
    vv
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
    cN
    cW
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg31.n
    cdlemg31b
    syl222anc
    adantr
    eqbrtrrd
    mtand
end
