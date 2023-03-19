include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "simp3.mm"
include "simp11.mm"
include "simp12l.mm"
include "simp13l.mm"
include "cdlemeulpq.mm"
include "syl12anc.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "wb.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp2rl.mm"
include "eqid.mm"
include "cdleme1b.mm"
include "syl13anc.mm"
include "cdleme0aa.mm"
include "syl3anc.mm"
include "hlatjcl.mm"
include "latjle12.mm"
include "biimpd.mm"
include "mpan2d.mm"
include "atbase.mm"
include "latlej1.mm"
include "cdleme35a.mm"
include "breqtrrd.mm"
include "wi.mm"
include "latjcl.mm"
include "lattr.mm"
include "mpand.mm"
include "syld.mm"
include "mtod.mm"

theorem cdleme35fnpq
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
  assume cdleme35.l: |- .<_ = ( le ` K )
  assume cdleme35.j: |- .\/ = ( join ` K )
  assume cdleme35.m: |- ./\ = ( meet ` K )
  assume cdleme35.a: |- A = ( Atoms ` K )
  assume cdleme35.h: |- H = ( LHyp ` K )
  assume cdleme35.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme35.f: |- F = ( ( R .\/ U ) ./\ ( Q .\/ ( ( P .\/ R ) ./\ W ) ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) ) /\ -. R .<_ ( P .\/ Q ) ) -> -. F .<_ ( P .\/ Q ) )

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
    cP
    cQ
    wne
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
    wa
    #
    cR
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
    cF
    @14
    c.le
    wbr
    #
    @15
    @9
    @13
    @16
    simp3
    @17
    @18
    cF
    cU
    c.or
    co
    #
    @14
    c.le
    wbr
    #
    @15
    @17
    @18
    cU
    @14
    c.le
    wbr
    #
    @20
    @17
    @2
    @3
    @6
    @21
    @2
    @5
    @8
    @13
    @16
    simp11
    #
    @3
    @4
    @2
    @8
    @13
    @16
    simp12l
    #
    @6
    @7
    @2
    @5
    @13
    @16
    simp13l
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
    cdleme35.l
    cdleme35.j
    cdleme35.m
    cdleme35.a
    cdleme35.h
    cdleme35.u
    cdlemeulpq
    syl12anc
    @17
    @18
    @21
    wa
    #
    @20
    @17
    cK
    clat
    wcel
    #
    cF
    cK
    cbs
    cfv
    #
    wcel
    #
    cU
    @27
    wcel
    #
    @14
    @27
    wcel
    #
    @25
    @20
    wb
    @17
    @0
    @26
    @0
    @1
    @5
    @8
    @13
    @16
    simp11l
    #
    cK
    hllat
    syl
    #
    @17
    @2
    @3
    @6
    @11
    @28
    @22
    @23
    @24
    @11
    @12
    @10
    @9
    @16
    simp2rl
    #
    cA
    @27
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
    cdleme35.l
    cdleme35.j
    cdleme35.m
    cdleme35.a
    cdleme35.h
    cdleme35.u
    cdleme35.f
    @27
    eqid
    #
    cdleme1b
    syl13anc
    #
    @17
    @2
    @3
    @6
    @29
    @22
    @23
    @24
    cA
    @27
    cP
    cQ
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme35.l
    cdleme35.j
    cdleme35.m
    cdleme35.a
    cdleme35.h
    cdleme35.u
    @34
    cdleme0aa
    syl3anc
    #
    @17
    @0
    @3
    @6
    @30
    @31
    @23
    @24
    cA
    @27
    c.or
    cK
    cP
    cQ
    @34
    cdleme35.j
    cdleme35.a
    hlatjcl
    syl3anc
    #
    @27
    c.or
    cK
    c.le
    cF
    cU
    @14
    @34
    cdleme35.l
    cdleme35.j
    latjle12
    syl13anc
    biimpd
    mpan2d
    @17
    cR
    @19
    c.le
    wbr
    #
    @20
    @15
    @17
    cR
    cR
    cU
    c.or
    co
    #
    @19
    c.le
    @17
    @26
    cR
    @27
    wcel
    #
    @29
    cR
    @39
    c.le
    wbr
    @32
    @17
    @11
    @40
    @33
    cA
    @27
    cR
    cK
    @34
    cdleme35.a
    atbase
    syl
    #
    @36
    @27
    c.or
    cK
    c.le
    cR
    cU
    @34
    cdleme35.l
    cdleme35.j
    latlej1
    syl3anc
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
    cdleme35.l
    cdleme35.j
    cdleme35.m
    cdleme35.a
    cdleme35.h
    cdleme35.u
    cdleme35.f
    cdleme35a
    breqtrrd
    @17
    @26
    @40
    @19
    @27
    wcel
    #
    @30
    @38
    @20
    wa
    @15
    wi
    @32
    @41
    @17
    @26
    @28
    @29
    @42
    @32
    @35
    @36
    @27
    c.or
    cK
    cF
    cU
    @34
    cdleme35.j
    latjcl
    syl3anc
    @37
    @27
    cK
    c.le
    cR
    @19
    @14
    @34
    cdleme35.l
    lattr
    syl13anc
    mpand
    syld
    mtod
end
