include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "cjn.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "cmee.mm"
include "simp123.mm"
include "fveq1d.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "simp11.mm"
include "simp131.mm"
include "simp22.mm"
include "simp121.mm"
include "simp33.mm"
include "simp132.mm"
include "simp23.mm"
include "simp31.mm"
include "eqid.mm"
include "cdlemi.mm"
include "syl323anc.mm"
include "simp122.mm"
include "3eqtr4d.mm"
include "simp133.mm"
include "simp21.mm"
include "simp32.mm"

theorem cdlemj1
  let cA: class A
  let cB: class B
  let cR: class R
  let cT: class T
  let cU: class U
  let vg: setvar g
  let vh: setvar h
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let vp: setvar p
  assume cdlemj.b: |- B = ( Base ` K )
  assume cdlemj.h: |- H = ( LHyp ` K )
  assume cdlemj.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemj.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemj.e: |- E = ( ( TEndo ` K ) ` W )
  assume cdlemj.l: |- .<_ = ( le ` K )
  assume cdlemj.a: |- A = ( Atoms ` K )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( U e. E /\ V e. E /\ ( U ` F ) = ( V ` F ) ) /\ ( F e. T /\ F =/= ( _I |` B ) /\ h e. T ) ) /\ ( h =/= ( _I |` B ) /\ g e. T /\ g =/= ( _I |` B ) ) /\ ( ( R ` F ) =/= ( R ` g ) /\ ( R ` g ) =/= ( R ` h ) /\ ( p e. A /\ -. p .<_ W ) ) ) -> ( ( U ` h ) ` p ) = ( ( V ` h ) ` p ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cU
    cE
    wcel
    #
    cV
    cE
    wcel
    #
    cF
    cU
    cfv
    #
    cF
    cV
    cfv
    #
    wceq
    #
    w3a
    #
    cF
    cT
    wcel
    #
    cF
    cid
    cB
    cres
    #
    wne
    #
    vh
    cv
    #
    cT
    wcel
    #
    w3a
    #
    w3a
    #
    @10
    @8
    wne
    #
    vg
    cv
    #
    cT
    wcel
    #
    @15
    @8
    wne
    #
    w3a
    #
    cF
    cR
    cfv
    @15
    cR
    cfv
    #
    wne
    #
    @19
    @10
    cR
    cfv
    #
    wne
    #
    vp
    cv
    #
    cA
    wcel
    @23
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    w3a
    #
    @23
    @21
    cK
    cjn
    cfv
    #
    co
    #
    @23
    @15
    cU
    cfv
    cfv
    #
    @10
    @15
    ccnv
    ccom
    cR
    cfv
    #
    @27
    co
    #
    cK
    cmee
    cfv
    #
    co
    #
    @28
    @23
    @15
    cV
    cfv
    cfv
    #
    @30
    @27
    co
    #
    @32
    co
    #
    @23
    @10
    cU
    cfv
    cfv
    #
    @23
    @10
    cV
    cfv
    cfv
    #
    @26
    @31
    @35
    @28
    @32
    @26
    @29
    @34
    @30
    @27
    @26
    @23
    @19
    @27
    co
    #
    @23
    @3
    cfv
    #
    @15
    cF
    ccnv
    ccom
    cR
    cfv
    #
    @27
    co
    #
    @32
    co
    #
    @39
    @23
    @4
    cfv
    #
    @41
    @27
    co
    #
    @32
    co
    #
    @29
    @34
    @26
    @42
    @45
    @39
    @32
    @26
    @40
    @44
    @41
    @27
    @26
    @23
    @3
    @4
    @1
    @2
    @5
    @0
    @12
    @18
    @25
    simp123
    fveq1d
    oveq1d
    oveq2d
    @26
    @0
    @7
    @16
    @1
    @24
    @9
    @17
    @20
    @29
    @43
    wceq
    @0
    @6
    @12
    @18
    @25
    simp11
    #
    @7
    @9
    @11
    @0
    @6
    @18
    @25
    simp131
    #
    @13
    @14
    @16
    @17
    @25
    simp22
    #
    @1
    @2
    @5
    @0
    @12
    @18
    @25
    simp121
    #
    @13
    @18
    @20
    @22
    @24
    simp33
    #
    @7
    @9
    @11
    @0
    @6
    @18
    @25
    simp132
    #
    @13
    @14
    @16
    @17
    @25
    simp23
    #
    @13
    @18
    @20
    @22
    @24
    simp31
    #
    cA
    cB
    @23
    cR
    @43
    cT
    cU
    cE
    cF
    @15
    cH
    @27
    cK
    c.le
    @32
    cW
    cdlemj.b
    cdlemj.l
    @27
    eqid
    #
    @32
    eqid
    #
    cdlemj.a
    cdlemj.h
    cdlemj.t
    cdlemj.r
    cdlemj.e
    @43
    eqid
    cdlemi
    syl323anc
    @26
    @0
    @7
    @16
    @2
    @24
    @9
    @17
    @20
    @34
    @46
    wceq
    @47
    @48
    @49
    @1
    @2
    @5
    @0
    @12
    @18
    @25
    simp122
    #
    @51
    @52
    @53
    @54
    cA
    cB
    @23
    cR
    @46
    cT
    cV
    cE
    cF
    @15
    cH
    @27
    cK
    c.le
    @32
    cW
    cdlemj.b
    cdlemj.l
    @55
    @56
    cdlemj.a
    cdlemj.h
    cdlemj.t
    cdlemj.r
    cdlemj.e
    @46
    eqid
    cdlemi
    syl323anc
    3eqtr4d
    oveq1d
    oveq2d
    @26
    @0
    @16
    @11
    @1
    @24
    @17
    @14
    @22
    @37
    @33
    wceq
    @47
    @49
    @7
    @9
    @11
    @0
    @6
    @18
    @25
    simp133
    #
    @50
    @51
    @53
    @13
    @14
    @16
    @17
    @25
    simp21
    #
    @13
    @18
    @20
    @22
    @24
    simp32
    #
    cA
    cB
    @23
    cR
    @33
    cT
    cU
    cE
    @15
    @10
    cH
    @27
    cK
    c.le
    @32
    cW
    cdlemj.b
    cdlemj.l
    @55
    @56
    cdlemj.a
    cdlemj.h
    cdlemj.t
    cdlemj.r
    cdlemj.e
    @33
    eqid
    cdlemi
    syl323anc
    @26
    @0
    @16
    @11
    @2
    @24
    @17
    @14
    @22
    @38
    @36
    wceq
    @47
    @49
    @58
    @57
    @51
    @53
    @59
    @60
    cA
    cB
    @23
    cR
    @36
    cT
    cV
    cE
    @15
    @10
    cH
    @27
    cK
    c.le
    @32
    cW
    cdlemj.b
    cdlemj.l
    @55
    @56
    cdlemj.a
    cdlemj.h
    cdlemj.t
    cdlemj.r
    cdlemj.e
    @36
    eqid
    cdlemi
    syl323anc
    3eqtr4d
end
