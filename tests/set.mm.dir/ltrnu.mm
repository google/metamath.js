include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "an4.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "simpr.mm"
include "simplr.mm"
include "cldil.mm"
include "wb.mm"
include "eqid.mm"
include "isltrn.mm"
include "ad2antrr.mm"
include "syl6bi.mm"
include "mpd.mm"
include "breq1.mm"
include "notbid.mm"
include "anbi1d.mm"
include "id.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "anbi2d.mm"
include "eqeq2d.mm"
include "rspc2v.mm"
include "sylc.mm"
include "impr.mm"
include "sylan2b.mm"
include "3impb.mm"

theorem ltrnu
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  let vp: setvar p
  let vq: setvar q
  assume ltrnu.l: |- .<_ = ( le ` K )
  assume ltrnu.j: |- .\/ = ( join ` K )
  assume ltrnu.m: |- ./\ = ( meet ` K )
  assume ltrnu.a: |- A = ( Atoms ` K )
  assume ltrnu.h: |- H = ( LHyp ` K )
  assume ltrnu.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( ( K e. V /\ W e. H ) /\ F e. T ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) -> ( ( P .\/ ( F ` P ) ) ./\ W ) = ( ( Q .\/ ( F ` Q ) ) ./\ W ) )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    #
    cF
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
    #
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
    #
    wn
    #
    wa
    #
    cP
    cP
    cF
    cfv
    #
    c.or
    co
    #
    cW
    c.an
    co
    #
    cQ
    cQ
    cF
    cfv
    #
    c.or
    co
    #
    cW
    c.an
    co
    #
    wceq
    #
    @6
    @10
    wa
    @2
    @3
    @7
    wa
    #
    @5
    @9
    wa
    #
    wa
    @17
    @3
    @5
    @7
    @9
    an4
    @2
    @18
    @19
    @17
    @2
    @18
    wa
    #
    @18
    vp
    cv
    #
    cW
    c.le
    wbr
    #
    wn
    #
    vq
    cv
    #
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    @21
    @21
    cF
    cfv
    #
    c.or
    co
    #
    cW
    c.an
    co
    #
    @24
    @24
    cF
    cfv
    #
    c.or
    co
    #
    cW
    c.an
    co
    #
    wceq
    #
    wi
    #
    vq
    cA
    wral
    vp
    cA
    wral
    #
    @19
    @17
    wi
    #
    @2
    @18
    simpr
    @20
    @1
    @36
    @0
    @1
    @18
    simplr
    @20
    @1
    cF
    cW
    cK
    cldil
    cfv
    cfv
    #
    wcel
    #
    @36
    wa
    #
    @36
    @0
    @1
    @40
    wb
    @1
    @18
    cA
    cV
    @38
    cT
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    vq
    vp
    ltrnu.l
    ltrnu.j
    ltrnu.m
    ltrnu.a
    ltrnu.h
    @38
    eqid
    ltrnu.t
    isltrn
    ad2antrr
    @39
    @36
    simpr
    syl6bi
    mpd
    @35
    @37
    @5
    @26
    wa
    #
    @13
    @33
    wceq
    #
    wi
    vp
    vq
    cP
    cQ
    cA
    cA
    @21
    cP
    wceq
    #
    @27
    @41
    @34
    @42
    @43
    @23
    @5
    @26
    @43
    @22
    @4
    @21
    cP
    cW
    c.le
    breq1
    notbid
    anbi1d
    @43
    @30
    @13
    @33
    @43
    @29
    @12
    cW
    c.an
    @43
    @21
    cP
    @28
    @11
    c.or
    @43
    id
    @21
    cP
    cF
    fveq2
    oveq12d
    oveq1d
    eqeq1d
    imbi12d
    @24
    cQ
    wceq
    #
    @41
    @19
    @42
    @17
    @44
    @26
    @9
    @5
    @44
    @25
    @8
    @24
    cQ
    cW
    c.le
    breq1
    notbid
    anbi2d
    @44
    @33
    @16
    @13
    @44
    @32
    @15
    cW
    c.an
    @44
    @24
    cQ
    @31
    @14
    c.or
    @44
    id
    @24
    cQ
    cF
    fveq2
    oveq12d
    oveq1d
    eqeq2d
    imbi12d
    rspc2v
    sylc
    impr
    sylan2b
    3impb
end
