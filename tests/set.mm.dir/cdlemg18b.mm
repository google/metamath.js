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
include "wi.mm"
include "simp3r.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp21.mm"
include "simp22l.mm"
include "simp3l1.mm"
include "cdleme0a.mm"
include "syl212anc.mm"
include "simp1.mm"
include "simp23.mm"
include "ltrnat.mm"
include "syl3anc.mm"
include "hlatlej1.mm"
include "clat.mm"
include "cbs.mm"
include "wb.mm"
include "hllat.mm"
include "syl.mm"
include "simp21l.mm"
include "eqid.mm"
include "atbase.mm"
include "hlatjcl.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "cdleme0cp.mm"
include "syl22anc.mm"
include "simp22.mm"
include "cdlemg2kq.mm"
include "syl121anc.mm"
include "hlatjcom.mm"
include "eqtr2d.mm"
include "3brtr3d.mm"
include "ps-1.mm"
include "syl132anc.mm"
include "mpbid.mm"
include "3exp.mm"
include "exp4a.mm"
include "3imp.mm"
include "necon3ad.mm"
include "mpd.mm"

theorem cdlemg18b
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cU: class U
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
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
  assume cdlemg18b.u: |- U = ( ( P .\/ Q ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ F e. T ) /\ ( P =/= Q /\ ( F ` P ) =/= Q /\ ( ( F ` Q ) .\/ ( F ` P ) ) =/= ( P .\/ Q ) ) ) -> -. P .<_ ( U .\/ ( F ` Q ) ) )

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
    cP
    cQ
    wne
    #
    cP
    cF
    cfv
    #
    cQ
    wne
    #
    cQ
    cF
    cfv
    #
    @12
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
    @17
    cP
    cU
    @14
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    @2
    @10
    @11
    @13
    @17
    simp33
    @19
    @21
    @15
    @16
    @2
    @10
    @18
    @21
    @15
    @16
    wceq
    #
    wi
    @2
    @10
    @18
    @21
    @22
    @2
    @10
    @18
    @21
    wa
    #
    @22
    @2
    @10
    @23
    w3a
    #
    @16
    @12
    @14
    c.or
    co
    #
    @15
    @24
    @16
    @25
    c.le
    wbr
    #
    @16
    @25
    wceq
    #
    @24
    cP
    cU
    c.or
    co
    #
    @20
    @16
    @25
    c.le
    @24
    @21
    cU
    @20
    c.le
    wbr
    #
    @28
    @20
    c.le
    wbr
    #
    @2
    @10
    @18
    @21
    simp3r
    @24
    @0
    cU
    cA
    wcel
    #
    @14
    cA
    wcel
    #
    @29
    @0
    @1
    @10
    @23
    simp1l
    #
    @24
    @0
    @1
    @5
    @6
    @11
    @31
    @33
    @0
    @1
    @10
    @23
    simp1r
    #
    @2
    @5
    @8
    @9
    @23
    simp21
    #
    @6
    @7
    @5
    @9
    @2
    @23
    simp22l
    #
    @11
    @13
    @17
    @21
    @2
    @10
    simp3l1
    #
    cA
    cP
    cQ
    cU
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
    cdlemg18b.u
    cdleme0a
    syl212anc
    #
    @24
    @2
    @9
    @6
    @32
    @2
    @10
    @23
    simp1
    #
    @2
    @5
    @8
    @9
    @23
    simp23
    #
    @36
    cA
    cQ
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
    ltrnat
    syl3anc
    #
    cA
    cU
    @14
    c.or
    cK
    c.le
    cdlemg12.l
    cdlemg12.j
    cdlemg12.a
    hlatlej1
    syl3anc
    @24
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
    cU
    @43
    wcel
    #
    @20
    @43
    wcel
    #
    @21
    @29
    wa
    @30
    wb
    @24
    @0
    @42
    @33
    cK
    hllat
    syl
    @24
    @3
    @44
    @3
    @4
    @8
    @9
    @2
    @23
    simp21l
    #
    cA
    @43
    cP
    cK
    @43
    eqid
    #
    cdlemg12.a
    atbase
    syl
    @24
    @31
    @45
    @38
    cA
    @43
    cU
    cK
    @48
    cdlemg12.a
    atbase
    syl
    @24
    @0
    @31
    @32
    @46
    @33
    @38
    @41
    cA
    @43
    c.or
    cK
    cU
    @14
    @48
    cdlemg12.j
    cdlemg12.a
    hlatjcl
    syl3anc
    @43
    c.or
    cK
    c.le
    cP
    cU
    @20
    @48
    cdlemg12.l
    cdlemg12.j
    latjle12
    syl13anc
    mpbi2and
    @24
    @0
    @1
    @5
    @6
    @28
    @16
    wceq
    @33
    @34
    @35
    @36
    cA
    cP
    cQ
    cU
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
    cdlemg18b.u
    cdleme0cp
    syl22anc
    @24
    @25
    @14
    cU
    c.or
    co
    #
    @20
    @24
    @2
    @5
    @8
    @9
    @25
    @49
    wceq
    @39
    @35
    @2
    @5
    @8
    @9
    @23
    simp22
    @40
    cA
    cP
    cQ
    cT
    cU
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg12.h
    cdlemg12.t
    cdlemg12.l
    cdlemg12.j
    cdlemg12.a
    cdlemg12.m
    cdlemg18b.u
    cdlemg2kq
    syl121anc
    @24
    @0
    @32
    @31
    @49
    @20
    wceq
    @33
    @41
    @38
    cA
    c.or
    cK
    @14
    cU
    cdlemg12.j
    cdlemg12.a
    hlatjcom
    syl3anc
    eqtr2d
    3brtr3d
    @24
    @0
    @3
    @6
    @11
    @12
    cA
    wcel
    #
    @32
    @26
    @27
    wb
    @33
    @47
    @36
    @37
    @24
    @2
    @9
    @3
    @50
    @39
    @40
    @47
    cA
    cP
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
    ltrnat
    syl3anc
    #
    @41
    cA
    cP
    cQ
    @12
    @14
    c.or
    cK
    c.le
    cdlemg12.l
    cdlemg12.j
    cdlemg12.a
    ps-1
    syl132anc
    mpbid
    @24
    @0
    @50
    @32
    @25
    @15
    wceq
    @33
    @51
    @41
    cA
    c.or
    cK
    @12
    @14
    cdlemg12.j
    cdlemg12.a
    hlatjcom
    syl3anc
    eqtr2d
    3exp
    exp4a
    3imp
    necon3ad
    mpd
end
