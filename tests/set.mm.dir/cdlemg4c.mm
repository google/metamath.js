include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "simpll.mm"
include "simplr2.mm"
include "simplr3.mm"
include "cdlemg4b2.mm"
include "syl3anc.mm"
include "simpr.mm"
include "clat.mm"
include "cbs.mm"
include "hllat.mm"
include "syl.mm"
include "simpr1l.mm"
include "eqid.mm"
include "atbase.mm"
include "simpl.mm"
include "simpr3.mm"
include "trlcl.mm"
include "syl2anc.mm"
include "syl5eqel.mm"
include "latlej2.mm"
include "adantr.mm"
include "wb.mm"
include "simpr2l.mm"
include "ltrncl.mm"
include "latjcl.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "eqbrtrrd.mm"
include "mpbird.mm"
include "simpld.mm"
include "ex.mm"
include "con3d.mm"
include "3impia.mm"

theorem cdlemg4c
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
  let cV: class V
  let cW: class W
  let vr: setvar r
  let cF: class F
  assume cdlemg4.l: |- .<_ = ( le ` K )
  assume cdlemg4.a: |- A = ( Atoms ` K )
  assume cdlemg4.h: |- H = ( LHyp ` K )
  assume cdlemg4.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg4.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemg4.j: |- .\/ = ( join ` K )
  assume cdlemg4b.v: |- V = ( R ` G )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ G e. T ) /\ -. Q .<_ ( P .\/ V ) ) -> -. ( G ` Q ) .<_ ( P .\/ V ) )

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
    cG
    cT
    wcel
    #
    w3a
    #
    cQ
    cP
    cV
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    cQ
    cG
    cfv
    #
    @11
    c.le
    wbr
    #
    wn
    @2
    @10
    wa
    #
    @14
    @12
    @15
    @14
    @12
    @15
    @14
    wa
    #
    @12
    @14
    @16
    @12
    @14
    wa
    #
    cQ
    @13
    c.or
    co
    #
    @11
    c.le
    wbr
    #
    @16
    @13
    cV
    c.or
    co
    #
    @18
    @11
    c.le
    @16
    @2
    @8
    @9
    @20
    @18
    wceq
    @2
    @10
    @14
    simpll
    #
    @5
    @8
    @9
    @2
    @14
    simplr2
    @5
    @8
    @9
    @2
    @14
    simplr3
    #
    cA
    cQ
    cR
    cT
    cG
    cH
    c.or
    cK
    c.le
    cV
    cW
    cdlemg4.l
    cdlemg4.a
    cdlemg4.h
    cdlemg4.t
    cdlemg4.r
    cdlemg4.j
    cdlemg4b.v
    cdlemg4b2
    syl3anc
    @16
    @14
    cV
    @11
    c.le
    wbr
    #
    @20
    @11
    c.le
    wbr
    #
    @15
    @14
    simpr
    @15
    @23
    @14
    @15
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
    cV
    @26
    wcel
    #
    @23
    @15
    @0
    @25
    @0
    @1
    @10
    simpll
    cK
    hllat
    syl
    #
    @15
    @3
    @27
    @3
    @4
    @8
    @9
    @2
    simpr1l
    cA
    @26
    cP
    cK
    @26
    eqid
    #
    cdlemg4.a
    atbase
    syl
    #
    @15
    cV
    cG
    cR
    cfv
    #
    @26
    cdlemg4b.v
    @15
    @2
    @9
    @32
    @26
    wcel
    #
    @2
    @10
    simpl
    #
    @2
    @5
    @8
    @9
    simpr3
    #
    @26
    cR
    cT
    cG
    cH
    cK
    cW
    @30
    cdlemg4.h
    cdlemg4.t
    cdlemg4.r
    trlcl
    #
    syl2anc
    syl5eqel
    #
    @26
    c.or
    cK
    c.le
    cP
    cV
    @30
    cdlemg4.l
    cdlemg4.j
    latlej2
    syl3anc
    adantr
    @15
    @14
    @23
    wa
    @24
    wb
    #
    @14
    @15
    @25
    @13
    @26
    wcel
    #
    @28
    @11
    @26
    wcel
    #
    @38
    @29
    @15
    @2
    @9
    cQ
    @26
    wcel
    #
    @39
    @34
    @35
    @15
    @6
    @41
    @6
    @7
    @5
    @9
    @2
    simpr2l
    cA
    @26
    cQ
    cK
    @30
    cdlemg4.a
    atbase
    syl
    #
    @26
    cT
    cG
    cH
    cK
    chlt
    cW
    cQ
    @30
    cdlemg4.h
    cdlemg4.t
    ltrncl
    syl3anc
    #
    @37
    @15
    @25
    @27
    @28
    @40
    @29
    @31
    @37
    @26
    c.or
    cK
    cP
    cV
    @30
    cdlemg4.j
    latjcl
    #
    syl3anc
    @26
    c.or
    cK
    c.le
    @13
    cV
    @11
    @30
    cdlemg4.l
    cdlemg4.j
    latjle12
    syl13anc
    adantr
    mpbi2and
    eqbrtrrd
    @16
    @25
    @41
    @39
    @40
    @17
    @19
    wb
    @15
    @25
    @14
    @29
    adantr
    #
    @15
    @41
    @14
    @42
    adantr
    @15
    @39
    @14
    @43
    adantr
    @16
    @25
    @27
    @28
    @40
    @45
    @15
    @27
    @14
    @31
    adantr
    @16
    cV
    @32
    @26
    cdlemg4b.v
    @16
    @2
    @9
    @33
    @21
    @22
    @36
    syl2anc
    syl5eqel
    @44
    syl3anc
    @26
    c.or
    cK
    c.le
    cQ
    @13
    @11
    @30
    cdlemg4.l
    cdlemg4.j
    latjle12
    syl13anc
    mpbird
    simpld
    ex
    con3d
    3impia
end
