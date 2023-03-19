include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "w3a.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "ccom.mm"
include "simp1.mm"
include "simp2.mm"
include "simp31.mm"
include "simp32.mm"
include "wb.mm"
include "simp21.mm"
include "simp23.mm"
include "tendoid0.mm"
include "syl112anc.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "simp33.mm"
include "simp22.mm"
include "cdleml2N.mm"
include "syl113anc.mm"
include "simpl1.mm"
include "simpr.mm"
include "simpl21.mm"
include "simpl23.mm"
include "tendocoval.mm"
include "syl121anc.mm"
include "eqeq1d.mm"
include "simp11.mm"
include "simp121.mm"
include "tendococl.mm"
include "syl3anc.mm"
include "simp122.mm"
include "simp3.mm"
include "simp123.mm"
include "simp131.mm"
include "tendocan.mm"
include "syl132anc.mm"
include "3expia.mm"
include "sylbird.mm"
include "reximdva.mm"
include "mpd.mm"

theorem cdleml3N
  let cB: class B
  let cR: class R
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let cE: class E
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vs: setvar s
  assume cdleml1.b: |- B = ( Base ` K )
  assume cdleml1.h: |- H = ( LHyp ` K )
  assume cdleml1.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdleml1.r: |- R = ( ( trL ` K ) ` W )
  assume cdleml1.e: |- E = ( ( TEndo ` K ) ` W )
  assume cdleml3.o: |- .0. = ( g e. T |-> ( _I |` B ) )

  disjoint E s
  disjoint K s
  disjoint R s
  disjoint T s
  disjoint U s
  disjoint V s
  disjoint W s
  disjoint f s
  disjoint g s
  disjoint B g
  disjoint B s
  disjoint E f
  disjoint f g
  disjoint H f
  disjoint H g
  disjoint H s
  disjoint K f
  disjoint K g
  disjoint .0. f
  disjoint .0. s
  disjoint T f
  disjoint T g
  disjoint U f
  disjoint V f
  disjoint W f
  disjoint W g
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( U e. E /\ V e. E /\ f e. T ) /\ ( f =/= ( _I |` B ) /\ U =/= .0. /\ V =/= .0. ) ) -> E. s e. E ( s o. U ) = V )

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
    vf
    cv
    #
    cT
    wcel
    #
    w3a
    #
    @3
    cid
    cB
    cres
    #
    wne
    #
    cU
    c.0
    wne
    #
    cV
    c.0
    wne
    #
    w3a
    #
    w3a
    #
    @3
    cU
    cfv
    #
    vs
    cv
    #
    cfv
    #
    @3
    cV
    cfv
    #
    wceq
    #
    vs
    cE
    wrex
    #
    @13
    cU
    ccom
    #
    cV
    wceq
    #
    vs
    cE
    wrex
    @11
    @0
    @5
    @7
    @12
    @6
    wne
    #
    @15
    @6
    wne
    #
    @17
    @0
    @5
    @10
    simp1
    #
    @0
    @5
    @10
    simp2
    @0
    @5
    @7
    @8
    @9
    simp31
    #
    @11
    @20
    @8
    @0
    @5
    @7
    @8
    @9
    simp32
    @11
    @12
    @6
    cU
    c.0
    @11
    @0
    @1
    @4
    @7
    @12
    @6
    wceq
    cU
    c.0
    wceq
    wb
    @22
    @0
    @1
    @2
    @4
    @10
    simp21
    @0
    @1
    @2
    @4
    @10
    simp23
    #
    @23
    cB
    cT
    cU
    vg
    cE
    @3
    cH
    cK
    c.0
    cW
    cdleml1.b
    cdleml1.h
    cdleml1.t
    cdleml1.e
    cdleml3.o
    tendoid0
    syl112anc
    necon3bid
    mpbird
    @11
    @21
    @9
    @0
    @5
    @7
    @8
    @9
    simp33
    @11
    @15
    @6
    cV
    c.0
    @11
    @0
    @2
    @4
    @7
    @15
    @6
    wceq
    cV
    c.0
    wceq
    wb
    @22
    @0
    @1
    @2
    @4
    @10
    simp22
    @24
    @23
    cB
    cT
    cV
    vg
    cE
    @3
    cH
    cK
    c.0
    cW
    cdleml1.b
    cdleml1.h
    cdleml1.t
    cdleml1.e
    cdleml3.o
    tendoid0
    syl112anc
    necon3bid
    mpbird
    cB
    cR
    cT
    cU
    vf
    cE
    cH
    cK
    cV
    cW
    vs
    cdleml1.b
    cdleml1.h
    cdleml1.t
    cdleml1.r
    cdleml1.e
    cdleml2N
    syl113anc
    @11
    @16
    @19
    vs
    cE
    @11
    @13
    cE
    wcel
    #
    wa
    #
    @16
    @3
    @18
    cfv
    #
    @15
    wceq
    #
    @19
    @26
    @27
    @14
    @15
    @26
    @0
    @25
    @1
    @4
    @27
    @14
    wceq
    @0
    @5
    @10
    @25
    simpl1
    @11
    @25
    simpr
    @1
    @2
    @4
    @0
    @10
    @25
    simpl21
    @1
    @2
    @4
    @0
    @10
    @25
    simpl23
    cT
    @13
    cE
    @3
    cH
    cK
    cU
    cW
    chlt
    cdleml1.h
    cdleml1.t
    cdleml1.e
    tendocoval
    syl121anc
    eqeq1d
    @11
    @25
    @28
    @19
    @11
    @25
    @28
    w3a
    #
    @0
    @18
    cE
    wcel
    #
    @2
    @28
    @4
    @7
    @19
    @0
    @5
    @10
    @25
    @28
    simp11
    #
    @29
    @0
    @25
    @1
    @30
    @31
    @11
    @25
    @28
    simp2
    @1
    @2
    @4
    @0
    @10
    @25
    @28
    simp121
    @13
    cU
    cE
    cH
    cK
    cW
    cdleml1.h
    cdleml1.e
    tendococl
    syl3anc
    @1
    @2
    @4
    @0
    @10
    @25
    @28
    simp122
    @11
    @25
    @28
    simp3
    @1
    @2
    @4
    @0
    @10
    @25
    @28
    simp123
    @7
    @8
    @9
    @0
    @5
    @25
    @28
    simp131
    cB
    cT
    @18
    cE
    @3
    cH
    cK
    cV
    cW
    cdleml1.b
    cdleml1.h
    cdleml1.t
    cdleml1.e
    tendocan
    syl132anc
    3expia
    sylbird
    reximdva
    mpd
end
