include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "ctrl.mm"
include "cfv.mm"
include "cple.mm"
include "eqid.mm"
include "simpl.mm"
include "wf.mm"
include "cv.mm"
include "ccnv.mm"
include "cmpt.mm"
include "simpll.mm"
include "tendocl.mm"
include "3expa.mm"
include "ltrncnv.mm"
include "syl2anc.mm"
include "fmptd.mm"
include "wceq.mm"
include "tendoi.mm"
include "adantl.mm"
include "feq1d.mm"
include "mpbird.mm"
include "w3a.mm"
include "ccom.mm"
include "simp1r.mm"
include "ltrnco.mm"
include "3adant1r.mm"
include "tendoi2.mm"
include "cnvco.mm"
include "ltrncom.mm"
include "fveq2d.mm"
include "simp1ll.mm"
include "simp1lr.mm"
include "simp3.mm"
include "simp2.mm"
include "tendovalco.mm"
include "syl32anc.mm"
include "eqtrd.mm"
include "cnveqd.mm"
include "coeq12d.mm"
include "3eqtr4a.mm"
include "adantll.mm"
include "trlcnv.mm"
include "wbr.mm"
include "tendotp.mm"
include "eqbrtrd.mm"
include "istendod.mm"

theorem tendoicl
  let cS: class S
  let cT: class T
  let vf: setvar f
  let cE: class E
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let vs: setvar s
  let vg: setvar g
  let vh: setvar h
  assume tendoicl.h: |- H = ( LHyp ` K )
  assume tendoicl.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendoicl.e: |- E = ( ( TEndo ` K ) ` W )
  assume tendoicl.i: |- I = ( s e. E |-> ( f e. T |-> `' ( s ` f ) ) )

  disjoint E s
  disjoint f s
  disjoint T f
  disjoint T s
  disjoint W f
  disjoint W s
  disjoint g h
  disjoint g s
  disjoint E g
  disjoint h s
  disjoint E h
  disjoint H g
  disjoint H h
  disjoint I g
  disjoint I h
  disjoint K g
  disjoint K h
  disjoint S g
  disjoint S h
  disjoint f g
  disjoint f h
  disjoint T g
  disjoint T h
  disjoint W g
  disjoint W h
  assert |- ( ( ( K e. HL /\ W e. H ) /\ S e. E ) -> ( I ` S ) e. E )

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
    cS
    cE
    wcel
    #
    wa
    #
    cW
    cK
    ctrl
    cfv
    cfv
    #
    cS
    cI
    cfv
    #
    cT
    vg
    vh
    cE
    cH
    cK
    cK
    cple
    cfv
    #
    chlt
    cW
    @7
    eqid
    #
    tendoicl.h
    tendoicl.t
    @5
    eqid
    #
    tendoicl.e
    @2
    @3
    simpl
    @4
    cT
    cT
    @6
    wf
    cT
    cT
    vg
    cT
    vg
    cv
    #
    cS
    cfv
    #
    ccnv
    #
    cmpt
    #
    wf
    @4
    vg
    cT
    @12
    cT
    @13
    @4
    @10
    cT
    wcel
    #
    wa
    #
    @2
    @11
    cT
    wcel
    #
    @12
    cT
    wcel
    @2
    @3
    @14
    simpll
    #
    @2
    @3
    @14
    @16
    cS
    cT
    cE
    @10
    cH
    cK
    chlt
    cW
    tendoicl.h
    tendoicl.t
    tendoicl.e
    tendocl
    3expa
    #
    cT
    @11
    cH
    cK
    cW
    tendoicl.h
    tendoicl.t
    ltrncnv
    syl2anc
    @13
    eqid
    fmptd
    @4
    cT
    cT
    @6
    @13
    @3
    @6
    @13
    wceq
    @2
    cS
    cT
    vf
    vg
    cE
    cI
    cK
    cW
    vs
    tendoicl.i
    tendoicl.t
    tendoi
    adantl
    feq1d
    mpbird
    @4
    @14
    vh
    cv
    #
    cT
    wcel
    #
    w3a
    #
    @10
    @19
    ccom
    #
    @6
    cfv
    #
    @22
    cS
    cfv
    #
    ccnv
    #
    @10
    @6
    cfv
    #
    @19
    @6
    cfv
    #
    ccom
    #
    @21
    @3
    @22
    cT
    wcel
    #
    @23
    @25
    wceq
    @2
    @3
    @14
    @20
    simp1r
    #
    @2
    @14
    @20
    @29
    @3
    cT
    @10
    @19
    cH
    cK
    cW
    tendoicl.h
    tendoicl.t
    ltrnco
    3adant1r
    cS
    cT
    vf
    cE
    @22
    cI
    cK
    cW
    vs
    tendoicl.i
    tendoicl.t
    tendoi2
    syl2anc
    @21
    @19
    cS
    cfv
    #
    @11
    ccom
    #
    ccnv
    @12
    @31
    ccnv
    #
    ccom
    @25
    @28
    @31
    @11
    cnvco
    @21
    @24
    @32
    @21
    @24
    @19
    @10
    ccom
    #
    cS
    cfv
    #
    @32
    @21
    @22
    @34
    cS
    @2
    @14
    @20
    @22
    @34
    wceq
    @3
    cT
    @10
    @19
    cH
    cK
    cW
    tendoicl.h
    tendoicl.t
    ltrncom
    3adant1r
    fveq2d
    @21
    @0
    @1
    @3
    @20
    @14
    @35
    @32
    wceq
    @0
    @1
    @3
    @14
    @20
    simp1ll
    @0
    @1
    @3
    @14
    @20
    simp1lr
    @30
    @4
    @14
    @20
    simp3
    #
    @4
    @14
    @20
    simp2
    #
    cS
    cT
    cE
    @19
    @10
    cH
    cK
    chlt
    cW
    tendoicl.h
    tendoicl.t
    tendoicl.e
    tendovalco
    syl32anc
    eqtrd
    cnveqd
    @21
    @26
    @12
    @27
    @33
    @21
    @3
    @14
    @26
    @12
    wceq
    #
    @30
    @37
    cS
    cT
    vf
    cE
    @10
    cI
    cK
    cW
    vs
    tendoicl.i
    tendoicl.t
    tendoi2
    #
    syl2anc
    @21
    @3
    @20
    @27
    @33
    wceq
    @30
    @36
    cS
    cT
    vf
    cE
    @19
    cI
    cK
    cW
    vs
    tendoicl.i
    tendoicl.t
    tendoi2
    syl2anc
    coeq12d
    3eqtr4a
    eqtrd
    @15
    @26
    @5
    cfv
    #
    @11
    @5
    cfv
    #
    @10
    @5
    cfv
    #
    @7
    @15
    @40
    @12
    @5
    cfv
    #
    @41
    @15
    @26
    @12
    @5
    @3
    @14
    @38
    @2
    @39
    adantll
    fveq2d
    @15
    @2
    @16
    @43
    @41
    wceq
    @17
    @18
    @5
    cT
    @11
    cH
    cK
    cW
    tendoicl.h
    tendoicl.t
    @9
    trlcnv
    syl2anc
    eqtrd
    @2
    @3
    @14
    @41
    @42
    @7
    wbr
    @5
    cS
    cT
    cE
    @10
    cH
    cK
    @7
    chlt
    cW
    @8
    tendoicl.h
    tendoicl.t
    @9
    tendoicl.e
    tendotp
    3expa
    eqbrtrd
    istendod
end
