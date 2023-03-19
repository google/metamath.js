include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "clat.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp21.mm"
include "atbase.mm"
include "simp23.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "simp22l.mm"
include "latjass.mm"
include "syl13anc.mm"
include "simp3l.mm"
include "simp3r.mm"
include "wi.mm"
include "latmlem1.mm"
include "mpd.mm"
include "latjlej2.mm"
include "eqbrtrrd.mm"
include "wb.mm"
include "latjcl.mm"
include "latleeqj2.mm"
include "mpbid.mm"
include "simp1.mm"
include "lhpmod2i2.mm"
include "syl121anc.mm"
include "oveq2d.mm"
include "cp1.mm"
include "cfv.mm"
include "simp22.mm"
include "eqid.mm"
include "lhpj1.mm"
include "syl2anc.mm"
include "col.mm"
include "hlol.mm"
include "olm11.mm"
include "eqtrd.mm"
include "latlej1.mm"
include "breqtrd.mm"
include "lattrd.mm"
include "latleeqj1.mm"
include "3eqtrd.mm"
include "3eqtr3d.mm"

theorem cdleme30a
  let cA: class A
  let cB: class B
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let cY: class Y
  let vs: setvar s
  assume cdleme30.b: |- B = ( Base ` K )
  assume cdleme30.l: |- .<_ = ( le ` K )
  assume cdleme30.j: |- .\/ = ( join ` K )
  assume cdleme30.m: |- ./\ = ( meet ` K )
  assume cdleme30.a: |- A = ( Atoms ` K )
  assume cdleme30.h: |- H = ( LHyp ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( s e. A /\ ( X e. B /\ -. X .<_ W ) /\ Y e. B ) /\ ( ( s .\/ ( X ./\ W ) ) = X /\ X .<_ Y ) ) -> ( s .\/ ( Y ./\ W ) ) = Y )

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
    vs
    cv
    #
    cA
    wcel
    #
    cX
    cB
    wcel
    #
    cX
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cY
    cB
    wcel
    #
    w3a
    #
    @3
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
    cX
    cY
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    @3
    cY
    cW
    c.an
    co
    #
    c.or
    co
    #
    cX
    c.or
    co
    #
    @3
    @16
    cX
    c.or
    co
    #
    c.or
    co
    #
    @17
    cY
    @15
    cK
    clat
    wcel
    #
    @3
    cB
    wcel
    #
    @16
    cB
    wcel
    #
    @5
    @18
    @20
    wceq
    @15
    @0
    @21
    @0
    @1
    @9
    @14
    simp1l
    #
    cK
    hllat
    syl
    #
    @15
    @4
    @22
    @2
    @4
    @7
    @8
    @14
    simp21
    cA
    cB
    @3
    cK
    cdleme30.b
    cdleme30.a
    atbase
    syl
    #
    @15
    @21
    @8
    cW
    cB
    wcel
    #
    @23
    @25
    @2
    @4
    @7
    @8
    @14
    simp23
    #
    @15
    @1
    @27
    @0
    @1
    @9
    @14
    simp1r
    cB
    cH
    cK
    cW
    cdleme30.b
    cdleme30.h
    lhpbase
    syl
    #
    cB
    cK
    c.an
    cY
    cW
    cdleme30.b
    cdleme30.m
    latmcl
    syl3anc
    #
    @5
    @6
    @4
    @8
    @2
    @14
    simp22l
    #
    cB
    c.or
    cK
    @3
    @16
    cX
    cdleme30.b
    cdleme30.j
    latjass
    syl13anc
    @15
    cX
    @17
    c.le
    wbr
    #
    @18
    @17
    wceq
    #
    @15
    @11
    cX
    @17
    c.le
    @2
    @9
    @12
    @13
    simp3l
    #
    @15
    @10
    @16
    c.le
    wbr
    #
    @11
    @17
    c.le
    wbr
    #
    @15
    @13
    @35
    @2
    @9
    @12
    @13
    simp3r
    #
    @15
    @21
    @5
    @8
    @27
    @13
    @35
    wi
    @25
    @31
    @28
    @29
    cB
    cK
    c.le
    c.an
    cX
    cY
    cW
    cdleme30.b
    cdleme30.l
    cdleme30.m
    latmlem1
    syl13anc
    mpd
    @15
    @21
    @10
    cB
    wcel
    #
    @23
    @22
    @35
    @36
    wi
    @25
    @15
    @21
    @5
    @27
    @38
    @25
    @31
    @29
    cB
    cK
    c.an
    cX
    cW
    cdleme30.b
    cdleme30.m
    latmcl
    syl3anc
    #
    @30
    @26
    cB
    c.or
    cK
    c.le
    @10
    @16
    @3
    cdleme30.b
    cdleme30.l
    cdleme30.j
    latjlej2
    syl13anc
    mpd
    eqbrtrrd
    @15
    @21
    @5
    @17
    cB
    wcel
    #
    @32
    @33
    wb
    @25
    @31
    @15
    @21
    @22
    @23
    @40
    @25
    @26
    @30
    cB
    c.or
    cK
    @3
    @16
    cdleme30.b
    cdleme30.j
    latjcl
    syl3anc
    cB
    c.or
    cK
    c.le
    cX
    @17
    cdleme30.b
    cdleme30.l
    cdleme30.j
    latleeqj2
    syl3anc
    mpbid
    @15
    @20
    @3
    cY
    cW
    cX
    c.or
    co
    #
    c.an
    co
    #
    c.or
    co
    @3
    cY
    c.or
    co
    #
    cY
    @15
    @19
    @42
    @3
    c.or
    @15
    @2
    @8
    @5
    @13
    @19
    @42
    wceq
    @2
    @9
    @14
    simp1
    #
    @28
    @31
    @37
    cB
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cY
    cX
    cdleme30.b
    cdleme30.l
    cdleme30.j
    cdleme30.m
    cdleme30.h
    lhpmod2i2
    syl121anc
    oveq2d
    @15
    @42
    cY
    @3
    c.or
    @15
    @42
    cY
    cK
    cp1
    cfv
    #
    c.an
    co
    #
    cY
    @15
    @41
    @45
    cY
    c.an
    @15
    @2
    @7
    @41
    @45
    wceq
    @44
    @2
    @4
    @7
    @8
    @14
    simp22
    cB
    @45
    cH
    c.or
    cK
    c.le
    cW
    cX
    cdleme30.b
    cdleme30.l
    cdleme30.j
    @45
    eqid
    #
    cdleme30.h
    lhpj1
    syl2anc
    oveq2d
    @15
    cK
    col
    wcel
    #
    @8
    @46
    cY
    wceq
    @15
    @0
    @48
    @24
    cK
    hlol
    syl
    @28
    cB
    @45
    cK
    c.an
    cY
    cdleme30.b
    cdleme30.m
    @47
    olm11
    syl2anc
    eqtrd
    oveq2d
    @15
    @3
    cY
    c.le
    wbr
    #
    @43
    cY
    wceq
    #
    @15
    cB
    cK
    c.le
    @3
    cX
    cY
    cdleme30.b
    cdleme30.l
    @25
    @26
    @31
    @28
    @15
    @3
    @11
    cX
    c.le
    @15
    @21
    @22
    @38
    @3
    @11
    c.le
    wbr
    @25
    @26
    @39
    cB
    c.or
    cK
    c.le
    @3
    @10
    cdleme30.b
    cdleme30.l
    cdleme30.j
    latlej1
    syl3anc
    @34
    breqtrd
    @37
    lattrd
    @15
    @21
    @22
    @8
    @49
    @50
    wb
    @25
    @26
    @28
    cB
    c.or
    cK
    c.le
    @3
    cY
    cdleme30.b
    cdleme30.l
    cdleme30.j
    latleeqj1
    syl3anc
    mpbid
    3eqtrd
    3eqtr3d
end
