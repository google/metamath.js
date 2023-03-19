include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "cmee.mm"
include "wceq.mm"
include "simp1.mm"
include "simp21.mm"
include "simp22.mm"
include "ltrniotacl.mm"
include "syl3anc.mm"
include "eqid.mm"
include "trlval2.mm"
include "ltrniotaval.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "clat.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp21l.mm"
include "atbase.mm"
include "simp23l.mm"
include "latlej1.mm"
include "simp3.mm"
include "wb.mm"
include "simp22l.mm"
include "latjcl.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "wi.mm"
include "hlatjcl.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latmlem1.mm"
include "mpd.mm"
include "eqbrtrd.mm"
include "simp23.mm"
include "lhple.mm"
include "breqtrd.mm"

theorem cdlemn2
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let vh: setvar h
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  assume cdlemn2.b: |- B = ( Base ` K )
  assume cdlemn2.l: |- .<_ = ( le ` K )
  assume cdlemn2.j: |- .\/ = ( join ` K )
  assume cdlemn2.a: |- A = ( Atoms ` K )
  assume cdlemn2.h: |- H = ( LHyp ` K )
  assume cdlemn2.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemn2.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemn2.f: |- F = ( iota_ h e. T ( h ` Q ) = S )

  disjoint .<_ h
  disjoint A h
  disjoint H h
  disjoint K h
  disjoint Q h
  disjoint S h
  disjoint T h
  disjoint W h
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( Q e. A /\ -. Q .<_ W ) /\ ( S e. A /\ -. S .<_ W ) /\ ( X e. B /\ X .<_ W ) ) /\ S .<_ ( Q .\/ X ) ) -> ( R ` F ) .<_ X )

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
    cS
    cA
    wcel
    #
    cS
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cX
    cB
    wcel
    #
    cX
    cW
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    cS
    cQ
    cX
    c.or
    co
    #
    c.le
    wbr
    #
    w3a
    #
    cF
    cR
    cfv
    #
    @13
    cW
    cK
    cmee
    cfv
    #
    co
    #
    cX
    c.le
    @15
    @16
    cQ
    cS
    c.or
    co
    #
    cW
    @17
    co
    #
    @18
    c.le
    @15
    @16
    cQ
    cQ
    cF
    cfv
    #
    c.or
    co
    #
    cW
    @17
    co
    #
    @20
    @15
    @2
    cF
    cT
    wcel
    #
    @5
    @16
    @23
    wceq
    @2
    @12
    @14
    simp1
    #
    @15
    @2
    @5
    @8
    @24
    @25
    @2
    @5
    @8
    @11
    @14
    simp21
    #
    @2
    @5
    @8
    @11
    @14
    simp22
    #
    cA
    cQ
    cS
    cT
    vh
    cF
    cH
    cK
    c.le
    cW
    cdlemn2.l
    cdlemn2.a
    cdlemn2.h
    cdlemn2.t
    cdlemn2.f
    ltrniotacl
    syl3anc
    @26
    cA
    cQ
    cR
    cT
    cF
    cH
    c.or
    cK
    c.le
    @17
    cW
    cdlemn2.l
    cdlemn2.j
    @17
    eqid
    #
    cdlemn2.a
    cdlemn2.h
    cdlemn2.t
    cdlemn2.r
    trlval2
    syl3anc
    @15
    @22
    @19
    cW
    @17
    @15
    @21
    cS
    cQ
    c.or
    @15
    @2
    @5
    @8
    @21
    cS
    wceq
    @25
    @26
    @27
    cA
    cQ
    cS
    cT
    vh
    cF
    cH
    cK
    c.le
    cW
    cdlemn2.l
    cdlemn2.a
    cdlemn2.h
    cdlemn2.t
    cdlemn2.f
    ltrniotaval
    syl3anc
    oveq2d
    oveq1d
    eqtrd
    @15
    @19
    @13
    c.le
    wbr
    #
    @20
    @18
    c.le
    wbr
    #
    @15
    cQ
    @13
    c.le
    wbr
    #
    @14
    @29
    @15
    cK
    clat
    wcel
    #
    cQ
    cB
    wcel
    #
    @9
    @31
    @15
    @0
    @32
    @0
    @1
    @12
    @14
    simp1l
    #
    cK
    hllat
    syl
    #
    @15
    @3
    @33
    @3
    @4
    @8
    @11
    @2
    @14
    simp21l
    #
    cA
    cB
    cQ
    cK
    cdlemn2.b
    cdlemn2.a
    atbase
    syl
    #
    @9
    @10
    @5
    @8
    @2
    @14
    simp23l
    #
    cB
    c.or
    cK
    c.le
    cQ
    cX
    cdlemn2.b
    cdlemn2.l
    cdlemn2.j
    latlej1
    syl3anc
    @2
    @12
    @14
    simp3
    @15
    @32
    @33
    cS
    cB
    wcel
    #
    @13
    cB
    wcel
    #
    @31
    @14
    wa
    @29
    wb
    @35
    @37
    @15
    @6
    @39
    @6
    @7
    @5
    @11
    @2
    @14
    simp22l
    #
    cA
    cB
    cS
    cK
    cdlemn2.b
    cdlemn2.a
    atbase
    syl
    @15
    @32
    @33
    @9
    @40
    @35
    @37
    @38
    cB
    c.or
    cK
    cQ
    cX
    cdlemn2.b
    cdlemn2.j
    latjcl
    syl3anc
    #
    cB
    c.or
    cK
    c.le
    cQ
    cS
    @13
    cdlemn2.b
    cdlemn2.l
    cdlemn2.j
    latjle12
    syl13anc
    mpbi2and
    @15
    @32
    @19
    cB
    wcel
    #
    @40
    cW
    cB
    wcel
    #
    @29
    @30
    wi
    @35
    @15
    @0
    @3
    @6
    @43
    @34
    @36
    @41
    cA
    cB
    c.or
    cK
    cQ
    cS
    cdlemn2.b
    cdlemn2.j
    cdlemn2.a
    hlatjcl
    syl3anc
    @42
    @15
    @1
    @44
    @0
    @1
    @12
    @14
    simp1r
    cB
    cH
    cK
    cW
    cdlemn2.b
    cdlemn2.h
    lhpbase
    syl
    cB
    cK
    c.le
    @17
    @19
    @13
    cW
    cdlemn2.b
    cdlemn2.l
    @28
    latmlem1
    syl13anc
    mpd
    eqbrtrd
    @15
    @2
    @5
    @11
    @18
    cX
    wceq
    @25
    @26
    @2
    @5
    @8
    @11
    @14
    simp23
    cA
    cB
    cQ
    cH
    c.or
    cK
    c.le
    @17
    cW
    cX
    cdlemn2.b
    cdlemn2.l
    cdlemn2.j
    @28
    cdlemn2.a
    cdlemn2.h
    lhple
    syl3anc
    breqtrd
end
