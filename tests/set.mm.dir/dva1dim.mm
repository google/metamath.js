include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "wbr.mm"
include "crab.mm"
include "w3a.mm"
include "tendocl.mm"
include "tendotp.mm"
include "jca.mm"
include "3expb.mm"
include "anass1rs.mm"
include "eleq1.mm"
include "fveq2.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "simpll.mm"
include "simplr.mm"
include "simprl.mm"
include "simprr.mm"
include "tendoex.mm"
include "syl121anc.mm"
include "eqcom.mm"
include "rexbii.mm"
include "sylib.mm"
include "ex.mm"
include "impbid.mm"
include "abbidv.mm"
include "df-rab.mm"
include "syl6eqr.mm"

theorem dva1dim
  let cR: class R
  let cT: class T
  let vg: setvar g
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vs: setvar s
  assume dva1dim.l: |- .<_ = ( le ` K )
  assume dva1dim.h: |- H = ( LHyp ` K )
  assume dva1dim.t: |- T = ( ( LTrn ` K ) ` W )
  assume dva1dim.r: |- R = ( ( trL ` K ) ` W )
  assume dva1dim.e: |- E = ( ( TEndo ` K ) ` W )

  disjoint .<_ s
  disjoint E s
  disjoint g s
  disjoint F g
  disjoint F s
  disjoint H g
  disjoint H s
  disjoint K g
  disjoint K s
  disjoint R s
  disjoint T g
  disjoint T s
  disjoint W g
  disjoint W s
  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T ) -> { g | E. s e. E g = ( s ` F ) } = { g e. T | ( R ` g ) .<_ ( R ` F ) } )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cF
    cT
    wcel
    #
    wa
    #
    vg
    cv
    #
    cF
    vs
    cv
    #
    cfv
    #
    wceq
    #
    vs
    cE
    wrex
    #
    vg
    cab
    @3
    cT
    wcel
    #
    @3
    cR
    cfv
    #
    cF
    cR
    cfv
    #
    c.le
    wbr
    #
    wa
    #
    vg
    cab
    @11
    vg
    cT
    crab
    @2
    @7
    @12
    vg
    @2
    @7
    @12
    @2
    @6
    @12
    vs
    cE
    @2
    @4
    cE
    wcel
    #
    wa
    @12
    @6
    @5
    cT
    wcel
    #
    @5
    cR
    cfv
    #
    @10
    c.le
    wbr
    #
    wa
    #
    @0
    @13
    @1
    @17
    @0
    @13
    @1
    @17
    @0
    @13
    @1
    w3a
    @14
    @16
    @4
    cT
    cE
    cF
    cH
    cK
    chlt
    cW
    dva1dim.h
    dva1dim.t
    dva1dim.e
    tendocl
    cR
    @4
    cT
    cE
    cF
    cH
    cK
    c.le
    chlt
    cW
    dva1dim.l
    dva1dim.h
    dva1dim.t
    dva1dim.r
    dva1dim.e
    tendotp
    jca
    3expb
    anass1rs
    @6
    @8
    @14
    @11
    @16
    @3
    @5
    cT
    eleq1
    @6
    @9
    @15
    @10
    c.le
    @3
    @5
    cR
    fveq2
    breq1d
    anbi12d
    syl5ibrcom
    rexlimdva
    @2
    @12
    @7
    @2
    @12
    wa
    #
    @5
    @3
    wceq
    #
    vs
    cE
    wrex
    #
    @7
    @18
    @0
    @1
    @8
    @11
    @20
    @0
    @1
    @12
    simpll
    @0
    @1
    @12
    simplr
    @2
    @8
    @11
    simprl
    @2
    @8
    @11
    simprr
    vs
    cR
    cT
    cE
    cF
    cH
    cK
    c.le
    @3
    cW
    dva1dim.l
    dva1dim.h
    dva1dim.t
    dva1dim.r
    dva1dim.e
    tendoex
    syl121anc
    @19
    @6
    vs
    cE
    @5
    @3
    eqcom
    rexbii
    sylib
    ex
    impbid
    abbidv
    @11
    vg
    cT
    df-rab
    syl6eqr
end
