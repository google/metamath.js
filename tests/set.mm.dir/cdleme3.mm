include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "eqid.mm"
include "cdleme3g.mm"
include "wceq.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp23l.mm"
include "atbase.mm"
include "cdleme3fa.mm"
include "latlej2.mm"
include "syl3anc.mm"
include "biantrurd.mm"
include "wb.mm"
include "hlatjcl.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "simp1.mm"
include "simp21l.mm"
include "simp22l.mm"
include "simp23.mm"
include "cdleme2.mm"
include "breq2d.mm"
include "bitrd.mm"
include "cal.mm"
include "hlatl.mm"
include "simp21.mm"
include "simp3l.mm"
include "lhpat2.mm"
include "syl112anc.mm"
include "atcmp.mm"
include "3bitrd.mm"
include "necon3bbid.mm"
include "mpbird.mm"

theorem cdleme3
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdleme1.l: |- .<_ = ( le ` K )
  assume cdleme1.j: |- .\/ = ( join ` K )
  assume cdleme1.m: |- ./\ = ( meet ` K )
  assume cdleme1.a: |- A = ( Atoms ` K )
  assume cdleme1.h: |- H = ( LHyp ` K )
  assume cdleme1.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme1.f: |- F = ( ( R .\/ U ) ./\ ( Q .\/ ( ( P .\/ R ) ./\ W ) ) )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( R e. A /\ -. R .<_ W ) ) /\ ( P =/= Q /\ -. R .<_ ( P .\/ Q ) ) ) -> -. F .<_ W )

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
    cR
    cA
    wcel
    #
    cR
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    cP
    cQ
    wne
    #
    cR
    cP
    cQ
    c.or
    co
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    cF
    cW
    c.le
    wbr
    #
    wn
    cF
    cU
    wne
    cA
    cP
    cQ
    cR
    cU
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cP
    cR
    c.or
    co
    cW
    c.an
    co
    #
    cW
    cdleme1.l
    cdleme1.j
    cdleme1.m
    cdleme1.a
    cdleme1.h
    cdleme1.u
    cdleme1.f
    @18
    eqid
    cdleme3g
    @16
    @17
    cF
    cU
    @16
    @17
    cF
    cR
    cF
    c.or
    co
    #
    c.le
    wbr
    #
    @17
    wa
    #
    cF
    cU
    c.le
    wbr
    #
    cF
    cU
    wceq
    #
    @16
    @20
    @17
    @16
    cK
    clat
    wcel
    #
    cR
    cK
    cbs
    cfv
    #
    wcel
    #
    cF
    @25
    wcel
    #
    @20
    @16
    @0
    @24
    @0
    @1
    @12
    @15
    simp1l
    #
    cK
    hllat
    syl
    #
    @16
    @9
    @26
    @9
    @10
    @5
    @8
    @2
    @15
    simp23l
    #
    cA
    @25
    cR
    cK
    @25
    eqid
    #
    cdleme1.a
    atbase
    syl
    @16
    cF
    cA
    wcel
    #
    @27
    cA
    cP
    cQ
    cR
    cU
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme1.l
    cdleme1.j
    cdleme1.m
    cdleme1.a
    cdleme1.h
    cdleme1.u
    cdleme1.f
    cdleme3fa
    #
    cA
    @25
    cF
    cK
    @31
    cdleme1.a
    atbase
    syl
    #
    @25
    c.or
    cK
    c.le
    cR
    cF
    @31
    cdleme1.l
    cdleme1.j
    latlej2
    syl3anc
    biantrurd
    @16
    @21
    cF
    @19
    cW
    c.an
    co
    #
    c.le
    wbr
    #
    @22
    @16
    @24
    @27
    @19
    @25
    wcel
    #
    cW
    @25
    wcel
    #
    @21
    @36
    wb
    @29
    @34
    @16
    @0
    @9
    @32
    @37
    @28
    @30
    @33
    cA
    @25
    c.or
    cK
    cR
    cF
    @31
    cdleme1.j
    cdleme1.a
    hlatjcl
    syl3anc
    @16
    @1
    @38
    @0
    @1
    @12
    @15
    simp1r
    @25
    cH
    cK
    cW
    @31
    cdleme1.h
    lhpbase
    syl
    @25
    cK
    c.le
    c.an
    cF
    @19
    cW
    @31
    cdleme1.l
    cdleme1.m
    latlem12
    syl13anc
    @16
    @35
    cU
    cF
    c.le
    @16
    @2
    @3
    @6
    @11
    @35
    cU
    wceq
    @2
    @12
    @15
    simp1
    #
    @3
    @4
    @8
    @11
    @2
    @15
    simp21l
    @6
    @7
    @5
    @11
    @2
    @15
    simp22l
    #
    @2
    @5
    @8
    @11
    @15
    simp23
    cA
    cP
    cQ
    cR
    cU
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme1.l
    cdleme1.j
    cdleme1.m
    cdleme1.a
    cdleme1.h
    cdleme1.u
    cdleme1.f
    cdleme2
    syl13anc
    breq2d
    bitrd
    @16
    cK
    cal
    wcel
    #
    @32
    cU
    cA
    wcel
    #
    @22
    @23
    wb
    @16
    @0
    @41
    @28
    cK
    hlatl
    syl
    @33
    @16
    @2
    @5
    @6
    @13
    @42
    @39
    @2
    @5
    @8
    @11
    @15
    simp21
    @40
    @2
    @12
    @13
    @14
    simp3l
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
    cdleme1.l
    cdleme1.j
    cdleme1.m
    cdleme1.a
    cdleme1.h
    cdleme1.u
    lhpat2
    syl112anc
    cA
    cF
    cU
    cK
    c.le
    cdleme1.l
    cdleme1.a
    atcmp
    syl3anc
    3bitrd
    necon3bbid
    mpbird
end
