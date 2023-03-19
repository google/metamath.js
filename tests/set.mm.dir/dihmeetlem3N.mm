include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wbr.mm"
include "w3a.mm"
include "wn.mm"
include "wceq.mm"
include "wne.mm"
include "simp2lr.mm"
include "wi.mm"
include "oveq1.mm"
include "simpr.mm"
include "sylan9eqr.mm"
include "clat.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp2ll.mm"
include "atbase.mm"
include "simp12l.mm"
include "simp12r.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latlej1.mm"
include "simp2r.mm"
include "breqtrd.mm"
include "simp3.mm"
include "wb.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "simp13.mm"
include "lattrd.mm"
include "3exp.mm"
include "syl7.mm"
include "exp4a.mm"
include "3imp.mm"
include "necon3bd.mm"
include "mpd.mm"

theorem dihmeetlem3N
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let cY: class Y
  assume dihmeetlem3.b: |- B = ( Base ` K )
  assume dihmeetlem3.l: |- .<_ = ( le ` K )
  assume dihmeetlem3.j: |- .\/ = ( join ` K )
  assume dihmeetlem3.m: |- ./\ = ( meet ` K )
  assume dihmeetlem3.a: |- A = ( Atoms ` K )
  assume dihmeetlem3.h: |- H = ( LHyp ` K )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ Y e. B ) /\ ( X ./\ Y ) .<_ W ) /\ ( ( Q e. A /\ -. Q .<_ W ) /\ ( Q .\/ ( X ./\ W ) ) = X ) /\ ( ( R e. A /\ -. R .<_ W ) /\ ( R .\/ ( Y ./\ W ) ) = Y ) ) -> Q =/= R )

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
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    cX
    cY
    c.an
    co
    #
    cW
    c.le
    wbr
    #
    w3a
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
    cQ
    cX
    cW
    c.an
    co
    #
    c.or
    co
    #
    cX
    wceq
    #
    wa
    #
    cR
    cA
    wcel
    cR
    cW
    c.le
    wbr
    wn
    wa
    #
    cR
    cY
    cW
    c.an
    co
    #
    c.or
    co
    #
    cY
    wceq
    #
    wa
    #
    w3a
    #
    @11
    cQ
    cR
    wne
    @9
    @11
    @15
    @8
    @21
    simp2lr
    @22
    @10
    cQ
    cR
    @8
    @16
    @21
    cQ
    cR
    wceq
    #
    @10
    wi
    @8
    @16
    @21
    @23
    @10
    @21
    @23
    wa
    cQ
    @18
    c.or
    co
    #
    cY
    wceq
    #
    @8
    @16
    @10
    @23
    @21
    @24
    @19
    cY
    cQ
    cR
    @18
    c.or
    oveq1
    @17
    @20
    simpr
    sylan9eqr
    @8
    @16
    @25
    @10
    @8
    @16
    @25
    w3a
    #
    cB
    cK
    c.le
    cQ
    @6
    cW
    dihmeetlem3.b
    dihmeetlem3.l
    @26
    @0
    cK
    clat
    wcel
    #
    @0
    @1
    @5
    @7
    @16
    @25
    simp11l
    cK
    hllat
    syl
    #
    @26
    @9
    cQ
    cB
    wcel
    #
    @9
    @11
    @15
    @8
    @25
    simp2ll
    cA
    cB
    cQ
    cK
    dihmeetlem3.b
    dihmeetlem3.a
    atbase
    syl
    #
    @26
    @27
    @3
    @4
    @6
    cB
    wcel
    @28
    @3
    @4
    @2
    @7
    @16
    @25
    simp12l
    #
    @3
    @4
    @2
    @7
    @16
    @25
    simp12r
    #
    cB
    cK
    c.an
    cX
    cY
    dihmeetlem3.b
    dihmeetlem3.m
    latmcl
    syl3anc
    @26
    @1
    cW
    cB
    wcel
    #
    @0
    @1
    @5
    @7
    @16
    @25
    simp11r
    cB
    cH
    cK
    cW
    dihmeetlem3.b
    dihmeetlem3.h
    lhpbase
    syl
    #
    @26
    cQ
    cX
    c.le
    wbr
    #
    cQ
    cY
    c.le
    wbr
    #
    cQ
    @6
    c.le
    wbr
    #
    @26
    cQ
    @14
    cX
    c.le
    @26
    @27
    @29
    @13
    cB
    wcel
    #
    cQ
    @14
    c.le
    wbr
    @28
    @30
    @26
    @27
    @3
    @33
    @38
    @28
    @31
    @34
    cB
    cK
    c.an
    cX
    cW
    dihmeetlem3.b
    dihmeetlem3.m
    latmcl
    syl3anc
    cB
    c.or
    cK
    c.le
    cQ
    @13
    dihmeetlem3.b
    dihmeetlem3.l
    dihmeetlem3.j
    latlej1
    syl3anc
    @8
    @12
    @15
    @25
    simp2r
    breqtrd
    @26
    cQ
    @24
    cY
    c.le
    @26
    @27
    @29
    @18
    cB
    wcel
    #
    cQ
    @24
    c.le
    wbr
    @28
    @30
    @26
    @27
    @4
    @33
    @39
    @28
    @32
    @34
    cB
    cK
    c.an
    cY
    cW
    dihmeetlem3.b
    dihmeetlem3.m
    latmcl
    syl3anc
    cB
    c.or
    cK
    c.le
    cQ
    @18
    dihmeetlem3.b
    dihmeetlem3.l
    dihmeetlem3.j
    latlej1
    syl3anc
    @8
    @16
    @25
    simp3
    breqtrd
    @26
    @27
    @29
    @3
    @4
    @35
    @36
    wa
    @37
    wb
    @28
    @30
    @31
    @32
    cB
    cK
    c.le
    c.an
    cQ
    cX
    cY
    dihmeetlem3.b
    dihmeetlem3.l
    dihmeetlem3.m
    latlem12
    syl13anc
    mpbi2and
    @2
    @5
    @7
    @16
    @25
    simp13
    lattrd
    3exp
    syl7
    exp4a
    3imp
    necon3bd
    mpd
end
