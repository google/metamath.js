include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "cpr.mm"
include "cv.mm"
include "ciin.mm"
include "cin.mm"
include "cdib.mm"
include "cglb.mm"
include "eqid.mm"
include "simp1l.mm"
include "simp2l.mm"
include "simp3l.mm"
include "meetval.mm"
include "fveq2d.mm"
include "cdm.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "simp1.mm"
include "dibeldmN.mm"
include "biimpar.mm"
include "3adant3.mm"
include "3adant2.mm"
include "wb.mm"
include "prssg.mm"
include "syl2anc.mm"
include "mpbi2and.mm"
include "prnzg.mm"
include "syl.mm"
include "dibglbN.mm"
include "syl12anc.mm"
include "eqtrd.mm"
include "clat.mm"
include "hllat.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latmle1.mm"
include "simp2r.mm"
include "lattrd.mm"
include "dihvalb.mm"
include "simpl1.mm"
include "wo.mm"
include "vex.mm"
include "elpr.mm"
include "simpl2.mm"
include "eleq1.mm"
include "breq1.mm"
include "anbi12d.mm"
include "adantl.mm"
include "mpbird.mm"
include "simpl3.mm"
include "jaodan.mm"
include "sylan2b.mm"
include "iineq2dv.mm"
include "3eqtr4d.mm"
include "fveq2.mm"
include "iinxprg.mm"

theorem dihmeetlem2N
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let vh: setvar h
  let cE: class E
  let cG: class G
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vq: setvar q
  let vx: setvar x
  assume dihmeetlem2.b: |- B = ( Base ` K )
  assume dihmeetlem2.m: |- ./\ = ( meet ` K )
  assume dihmeetlem2.h: |- H = ( LHyp ` K )
  assume dihmeetlem2.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihmeetlem2.l: |- .<_ = ( le ` K )
  assume dihmeetlem2.j: |- .\/ = ( join ` K )
  assume dihmeetlem2.a: |- A = ( Atoms ` K )
  assume dihmeetlem2.p: |- P = ( ( oc ` K ) ` W )
  assume dihmeetlem2.t: |- T = ( ( LTrn ` K ) ` W )
  assume dihmeetlem2.r: |- R = ( ( trL ` K ) ` W )
  assume dihmeetlem2.e: |- E = ( ( TEndo ` K ) ` W )
  assume dihmeetlem2.g: |- G = ( iota_ h e. T ( h ` P ) = q )
  assume dihmeetlem2.o: |- .0. = ( h e. T |-> ( _I |` B ) )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ X .<_ W ) /\ ( Y e. B /\ Y .<_ W ) ) -> ( I ` ( X ./\ Y ) ) = ( ( I ` X ) i^i ( I ` Y ) ) )

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
    cX
    cW
    c.le
    wbr
    #
    wa
    #
    cY
    cB
    wcel
    #
    cY
    cW
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    cX
    cY
    c.an
    co
    #
    cI
    cfv
    #
    vx
    cX
    cY
    cpr
    #
    vx
    cv
    #
    cI
    cfv
    #
    ciin
    #
    cX
    cI
    cfv
    #
    cY
    cI
    cfv
    #
    cin
    #
    @9
    @10
    cW
    cK
    cdib
    cfv
    cfv
    #
    cfv
    #
    vx
    @12
    @13
    @19
    cfv
    #
    ciin
    #
    @11
    @15
    @9
    @20
    @12
    cK
    cglb
    cfv
    #
    cfv
    #
    @19
    cfv
    #
    @22
    @9
    @10
    @24
    @19
    @9
    @23
    cK
    c.an
    chlt
    cB
    cX
    cY
    cB
    @23
    eqid
    #
    dihmeetlem2.m
    @0
    @1
    @5
    @8
    simp1l
    #
    @2
    @3
    @4
    @8
    simp2l
    #
    @2
    @5
    @6
    @7
    simp3l
    #
    meetval
    fveq2d
    @9
    @2
    @12
    @19
    cdm
    #
    wss
    #
    @12
    c0
    wne
    #
    @25
    @22
    wceq
    @2
    @5
    @8
    simp1
    #
    @9
    cX
    @30
    wcel
    #
    cY
    @30
    wcel
    #
    @31
    @2
    @5
    @34
    @8
    @2
    @34
    @5
    cB
    cH
    @19
    cK
    c.le
    chlt
    cW
    cX
    dihmeetlem2.b
    dihmeetlem2.l
    dihmeetlem2.h
    @19
    eqid
    #
    dibeldmN
    biimpar
    3adant3
    @2
    @8
    @35
    @5
    @2
    @35
    @8
    cB
    cH
    @19
    cK
    c.le
    chlt
    cW
    cY
    dihmeetlem2.b
    dihmeetlem2.l
    dihmeetlem2.h
    @36
    dibeldmN
    biimpar
    3adant2
    @9
    @3
    @6
    @34
    @35
    wa
    @31
    wb
    @28
    @29
    cX
    cY
    @30
    cB
    cB
    prssg
    syl2anc
    mpbi2and
    @9
    @3
    @32
    @28
    cX
    cY
    cB
    prnzg
    syl
    vx
    @12
    @23
    cH
    @19
    cK
    cW
    @26
    dihmeetlem2.h
    @36
    dibglbN
    syl12anc
    eqtrd
    @9
    @2
    @10
    cB
    wcel
    #
    @10
    cW
    c.le
    wbr
    @11
    @20
    wceq
    @33
    @9
    cK
    clat
    wcel
    #
    @3
    @6
    @37
    @9
    @0
    @38
    @27
    cK
    hllat
    syl
    #
    @28
    @29
    cB
    cK
    c.an
    cX
    cY
    dihmeetlem2.b
    dihmeetlem2.m
    latmcl
    syl3anc
    #
    @9
    cB
    cK
    c.le
    @10
    cX
    cW
    dihmeetlem2.b
    dihmeetlem2.l
    @39
    @40
    @28
    @9
    @1
    cW
    cB
    wcel
    @0
    @1
    @5
    @8
    simp1r
    cB
    cH
    cK
    cW
    dihmeetlem2.b
    dihmeetlem2.h
    lhpbase
    syl
    @9
    @38
    @3
    @6
    @10
    cX
    c.le
    wbr
    @39
    @28
    @29
    cB
    cK
    c.le
    c.an
    cX
    cY
    dihmeetlem2.b
    dihmeetlem2.l
    dihmeetlem2.m
    latmle1
    syl3anc
    @2
    @3
    @4
    @8
    simp2r
    lattrd
    cB
    @19
    cH
    cI
    cK
    c.le
    chlt
    cW
    @10
    dihmeetlem2.b
    dihmeetlem2.l
    dihmeetlem2.h
    dihmeetlem2.i
    @36
    dihvalb
    syl12anc
    @9
    vx
    @12
    @14
    @21
    @9
    @13
    @12
    wcel
    #
    wa
    @2
    @13
    cB
    wcel
    #
    @13
    cW
    c.le
    wbr
    #
    wa
    #
    @14
    @21
    wceq
    @2
    @5
    @8
    @41
    simpl1
    @41
    @9
    @13
    cX
    wceq
    #
    @13
    cY
    wceq
    #
    wo
    @44
    @13
    cX
    cY
    vx
    vex
    elpr
    @9
    @45
    @44
    @46
    @9
    @45
    wa
    @44
    @5
    @2
    @5
    @8
    @45
    simpl2
    @45
    @44
    @5
    wb
    @9
    @45
    @42
    @3
    @43
    @4
    @13
    cX
    cB
    eleq1
    @13
    cX
    cW
    c.le
    breq1
    anbi12d
    adantl
    mpbird
    @9
    @46
    wa
    @44
    @8
    @2
    @5
    @8
    @46
    simpl3
    @46
    @44
    @8
    wb
    @9
    @46
    @42
    @6
    @43
    @7
    @13
    cY
    cB
    eleq1
    @13
    cY
    cW
    c.le
    breq1
    anbi12d
    adantl
    mpbird
    jaodan
    sylan2b
    cB
    @19
    cH
    cI
    cK
    c.le
    chlt
    cW
    @13
    dihmeetlem2.b
    dihmeetlem2.l
    dihmeetlem2.h
    dihmeetlem2.i
    @36
    dihvalb
    syl2anc
    iineq2dv
    3eqtr4d
    @9
    @3
    @6
    @15
    @18
    wceq
    @28
    @29
    vx
    cX
    cY
    @14
    @16
    @17
    cB
    cB
    @13
    cX
    cI
    fveq2
    @13
    cY
    cI
    fveq2
    iinxprg
    syl2anc
    eqtrd
end
