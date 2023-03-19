include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "clat.mm"
include "simpl1l.mm"
include "hllat.mm"
include "syl.mm"
include "simpl1.mm"
include "simprlr.mm"
include "trlcl.mm"
include "syl2anc.mm"
include "simpl2l.mm"
include "simpl3l.mm"
include "simprr.mm"
include "simprll.mm"
include "lattrd.mm"
include "exp44.mm"
include "ralrimdv.mm"
include "simp11l.mm"
include "simp2r.mm"
include "atbase.mm"
include "simp12l.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "simp3.mm"
include "simp12r.mm"
include "jca.mm"
include "3expia.mm"
include "wceq.mm"
include "wrex.mm"
include "simp11.mm"
include "cdlemf.mm"
include "syl12anc.mm"
include "simp2l.mm"
include "weq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "rspccv.mm"
include "breq1.mm"
include "biimpcd.mm"
include "syl6.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "impd.mm"
include "syld.mm"
include "exp32.mm"
include "wb.mm"
include "simp1l.mm"
include "simp3l.mm"
include "hlatle.mm"
include "syl3anc.mm"
include "sylibrd.mm"
include "impbid.mm"

theorem trlord
  let cA: class A
  let cB: class B
  let cR: class R
  let cT: class T
  let vf: setvar f
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let cY: class Y
  let vg: setvar g
  let vu: setvar u
  assume trlord.b: |- B = ( Base ` K )
  assume trlord.l: |- .<_ = ( le ` K )
  assume trlord.a: |- A = ( Atoms ` K )
  assume trlord.h: |- H = ( LHyp ` K )
  assume trlord.t: |- T = ( ( LTrn ` K ) ` W )
  assume trlord.r: |- R = ( ( trL ` K ) ` W )

  disjoint .<_ f
  disjoint B f
  disjoint H f
  disjoint K f
  disjoint R f
  disjoint T f
  disjoint W f
  disjoint X f
  disjoint Y f
  disjoint f g
  disjoint f u
  disjoint g u
  disjoint .<_ g
  disjoint .<_ u
  disjoint A g
  disjoint A u
  disjoint B g
  disjoint B u
  disjoint H g
  disjoint H u
  disjoint K g
  disjoint K u
  disjoint R g
  disjoint R u
  disjoint T g
  disjoint T u
  disjoint W g
  disjoint W u
  disjoint X g
  disjoint X u
  disjoint Y g
  disjoint Y u
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ X .<_ W ) /\ ( Y e. B /\ Y .<_ W ) ) -> ( X .<_ Y <-> A. f e. T ( ( R ` f ) .<_ X -> ( R ` f ) .<_ Y ) ) )

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
    c.le
    wbr
    #
    vf
    cv
    #
    cR
    cfv
    #
    cX
    c.le
    wbr
    #
    @12
    cY
    c.le
    wbr
    #
    wi
    #
    vf
    cT
    wral
    #
    @9
    @10
    @15
    vf
    cT
    @9
    @10
    @11
    cT
    wcel
    #
    @13
    @14
    @9
    @10
    @17
    wa
    #
    @13
    wa
    #
    wa
    #
    cB
    cK
    c.le
    @12
    cX
    cY
    trlord.b
    trlord.l
    @20
    @0
    cK
    clat
    wcel
    #
    @0
    @1
    @5
    @8
    @19
    simpl1l
    cK
    hllat
    #
    syl
    @20
    @2
    @17
    @12
    cB
    wcel
    @2
    @5
    @8
    @19
    simpl1
    @9
    @10
    @17
    @13
    simprlr
    cB
    cR
    cT
    @11
    cH
    cK
    cW
    trlord.b
    trlord.h
    trlord.t
    trlord.r
    trlcl
    syl2anc
    @3
    @4
    @2
    @8
    @19
    simpl2l
    @6
    @7
    @2
    @5
    @19
    simpl3l
    @9
    @18
    @13
    simprr
    @9
    @10
    @17
    @13
    simprll
    lattrd
    exp44
    ralrimdv
    @9
    @16
    vu
    cv
    #
    cX
    c.le
    wbr
    #
    @23
    cY
    c.le
    wbr
    #
    wi
    #
    vu
    cA
    wral
    #
    @10
    @9
    @16
    @26
    vu
    cA
    @9
    @16
    @23
    cA
    wcel
    #
    @26
    @9
    @16
    @28
    wa
    #
    wa
    #
    @24
    @23
    cW
    c.le
    wbr
    #
    @24
    wa
    #
    @25
    @9
    @29
    @24
    @32
    @9
    @29
    @24
    w3a
    #
    @31
    @24
    @33
    cB
    cK
    c.le
    @23
    cX
    cW
    trlord.b
    trlord.l
    @33
    @0
    @21
    @0
    @1
    @5
    @8
    @29
    @24
    simp11l
    @22
    syl
    @33
    @28
    @23
    cB
    wcel
    @9
    @16
    @28
    @24
    simp2r
    cA
    cB
    @23
    cK
    trlord.b
    trlord.a
    atbase
    syl
    @3
    @4
    @2
    @8
    @29
    @24
    simp12l
    @33
    @1
    cW
    cB
    wcel
    @0
    @1
    @5
    @8
    @29
    @24
    simp11r
    cB
    cH
    cK
    cW
    trlord.b
    trlord.h
    lhpbase
    syl
    @9
    @29
    @24
    simp3
    #
    @3
    @4
    @2
    @8
    @29
    @24
    simp12r
    lattrd
    @34
    jca
    3expia
    @30
    @31
    @24
    @25
    @9
    @29
    @31
    @26
    @9
    @29
    @31
    w3a
    #
    vg
    cv
    #
    cR
    cfv
    #
    @23
    wceq
    #
    vg
    cT
    wrex
    #
    @26
    @35
    @2
    @28
    @31
    @39
    @2
    @5
    @8
    @29
    @31
    simp11
    @9
    @16
    @28
    @31
    simp2r
    @9
    @29
    @31
    simp3
    cA
    cR
    cT
    @23
    vg
    cH
    cK
    c.le
    cW
    trlord.l
    trlord.a
    trlord.h
    trlord.t
    trlord.r
    cdlemf
    syl12anc
    @35
    @38
    @26
    vg
    cT
    @35
    @36
    cT
    wcel
    #
    @37
    cX
    c.le
    wbr
    #
    @37
    cY
    c.le
    wbr
    #
    wi
    #
    @38
    @26
    wi
    @35
    @16
    @40
    @43
    wi
    @9
    @16
    @28
    @31
    simp2l
    @15
    @43
    vf
    @36
    cT
    vf
    vg
    weq
    #
    @13
    @41
    @14
    @42
    @44
    @12
    @37
    cX
    c.le
    @11
    @36
    cR
    fveq2
    #
    breq1d
    @44
    @12
    @37
    cY
    c.le
    @45
    breq1d
    imbi12d
    rspccv
    syl
    @38
    @43
    @26
    @38
    @41
    @24
    @42
    @25
    @37
    @23
    cX
    c.le
    breq1
    @37
    @23
    cY
    c.le
    breq1
    imbi12d
    biimpcd
    syl6
    rexlimdv
    mpd
    3expia
    impd
    syld
    exp32
    ralrimdv
    @9
    @0
    @3
    @6
    @10
    @27
    wb
    @0
    @1
    @5
    @8
    simp1l
    @2
    @3
    @4
    @8
    simp2l
    @2
    @5
    @6
    @7
    simp3l
    cA
    cB
    cK
    c.le
    cX
    cY
    vu
    trlord.b
    trlord.l
    trlord.a
    hlatle
    syl3anc
    sylibrd
    impbid
end
