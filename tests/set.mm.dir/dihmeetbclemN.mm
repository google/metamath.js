include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wbr.mm"
include "w3a.mm"
include "cfv.mm"
include "cin.mm"
include "wceq.mm"
include "simp3.mm"
include "clat.mm"
include "wb.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp2l.mm"
include "simp2r.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latleeqm1.mm"
include "mpbid.mm"
include "col.mm"
include "hlol.mm"
include "latmassOLD.mm"
include "syl13anc.mm"
include "eqtr3d.mm"
include "fveq2d.mm"
include "simp1.mm"
include "latmle2.mm"
include "dihmeetbN.mm"
include "syl112anc.mm"
include "latref.mm"
include "syl2anc.mm"
include "ineq2d.mm"
include "3eqtrd.mm"
include "inass.mm"
include "syl6eqr.mm"

theorem dihmeetbclemN
  let cB: class B
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let cY: class Y
  let vg: setvar g
  let vq: setvar q
  let vx: setvar x
  assume dihmeetc.b: |- B = ( Base ` K )
  assume dihmeetc.l: |- .<_ = ( le ` K )
  assume dihmeetc.m: |- ./\ = ( meet ` K )
  assume dihmeetc.h: |- H = ( LHyp ` K )
  assume dihmeetc.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ Y e. B ) /\ ( X ./\ Y ) .<_ W ) -> ( I ` ( X ./\ Y ) ) = ( ( ( I ` X ) i^i ( I ` Y ) ) i^i ( I ` W ) ) )

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
    @6
    cI
    cfv
    #
    cX
    cI
    cfv
    #
    cY
    cI
    cfv
    #
    cW
    cI
    cfv
    #
    cin
    #
    cin
    #
    @10
    @11
    cin
    @12
    cin
    @8
    @9
    cX
    cY
    cW
    c.an
    co
    #
    c.an
    co
    #
    cI
    cfv
    #
    @10
    @15
    cI
    cfv
    #
    cin
    #
    @14
    @8
    @6
    @16
    cI
    @8
    @6
    cW
    c.an
    co
    #
    @6
    @16
    @8
    @7
    @20
    @6
    wceq
    #
    @2
    @5
    @7
    simp3
    @8
    cK
    clat
    wcel
    #
    @6
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    @7
    @21
    wb
    @8
    @0
    @22
    @0
    @1
    @5
    @7
    simp1l
    #
    cK
    hllat
    syl
    #
    @8
    @22
    @3
    @4
    @23
    @26
    @2
    @3
    @4
    @7
    simp2l
    #
    @2
    @3
    @4
    @7
    simp2r
    #
    cB
    cK
    c.an
    cX
    cY
    dihmeetc.b
    dihmeetc.m
    latmcl
    syl3anc
    @8
    @1
    @24
    @0
    @1
    @5
    @7
    simp1r
    cB
    cH
    cK
    cW
    dihmeetc.b
    dihmeetc.h
    lhpbase
    syl
    #
    cB
    cK
    c.le
    c.an
    @6
    cW
    dihmeetc.b
    dihmeetc.l
    dihmeetc.m
    latleeqm1
    syl3anc
    mpbid
    @8
    cK
    col
    wcel
    #
    @3
    @4
    @24
    @20
    @16
    wceq
    @8
    @0
    @30
    @25
    cK
    hlol
    syl
    @27
    @28
    @29
    cB
    cK
    c.an
    cX
    cY
    cW
    dihmeetc.b
    dihmeetc.m
    latmassOLD
    syl13anc
    eqtr3d
    fveq2d
    @8
    @2
    @3
    @15
    cB
    wcel
    #
    @15
    cW
    c.le
    wbr
    #
    @17
    @19
    wceq
    @2
    @5
    @7
    simp1
    #
    @27
    @8
    @22
    @4
    @24
    @31
    @26
    @28
    @29
    cB
    cK
    c.an
    cY
    cW
    dihmeetc.b
    dihmeetc.m
    latmcl
    syl3anc
    @8
    @22
    @4
    @24
    @32
    @26
    @28
    @29
    cB
    cK
    c.le
    c.an
    cY
    cW
    dihmeetc.b
    dihmeetc.l
    dihmeetc.m
    latmle2
    syl3anc
    cB
    cH
    cI
    cK
    c.le
    c.an
    cW
    cX
    @15
    dihmeetc.b
    dihmeetc.l
    dihmeetc.m
    dihmeetc.h
    dihmeetc.i
    dihmeetbN
    syl112anc
    @8
    @18
    @13
    @10
    @8
    @2
    @4
    @24
    cW
    cW
    c.le
    wbr
    #
    @18
    @13
    wceq
    @33
    @28
    @29
    @8
    @22
    @24
    @34
    @26
    @29
    cB
    cK
    c.le
    cW
    dihmeetc.b
    dihmeetc.l
    latref
    syl2anc
    cB
    cH
    cI
    cK
    c.le
    c.an
    cW
    cY
    cW
    dihmeetc.b
    dihmeetc.l
    dihmeetc.m
    dihmeetc.h
    dihmeetc.i
    dihmeetbN
    syl112anc
    ineq2d
    3eqtrd
    @10
    @11
    @12
    inass
    syl6eqr
end
