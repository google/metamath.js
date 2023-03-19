include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cop.mm"
include "wceq.mm"
include "wrex.mm"
include "c1st.mm"
include "wbr.mm"
include "c2nd.mm"
include "cxp.mm"
include "wb.mm"
include "eqop.mm"
include "adantl.mm"
include "rexbidv.mm"
include "r19.41v.mm"
include "crab.mm"
include "cab.mm"
include "fvex.mm"
include "eqeq1.mm"
include "elab.mm"
include "dva1dim.mm"
include "adantr.mm"
include "eleq2d.mm"
include "syl5bbr.mm"
include "xp1st.mm"
include "fveq2.mm"
include "breq1d.mm"
include "elrab3.mm"
include "syl.mm"
include "bitrd.mm"
include "anbi1d.mm"
include "syl5bb.mm"
include "rabbidva.mm"

theorem dvhb1dimN
  let cB: class B
  let cR: class R
  let cT: class T
  let vg: setvar g
  let vh: setvar h
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let c.0: class .0.
  let vs: setvar s
  let vf: setvar f
  assume dvhb1dim.l: |- .<_ = ( le ` K )
  assume dvhb1dim.h: |- H = ( LHyp ` K )
  assume dvhb1dim.t: |- T = ( ( LTrn ` K ) ` W )
  assume dvhb1dim.r: |- R = ( ( trL ` K ) ` W )
  assume dvhb1dim.e: |- E = ( ( TEndo ` K ) ` W )
  assume dvhb1dim.o: |- .0. = ( h e. T |-> ( _I |` B ) )

  disjoint .<_ s
  disjoint E s
  disjoint g s
  disjoint F g
  disjoint F s
  disjoint H g
  disjoint H s
  disjoint K g
  disjoint K s
  disjoint .0. s
  disjoint R s
  disjoint g h
  disjoint T g
  disjoint h s
  disjoint T h
  disjoint T s
  disjoint W g
  disjoint W s
  disjoint f s
  disjoint .<_ f
  disjoint E f
  disjoint f g
  disjoint F f
  disjoint H f
  disjoint K f
  disjoint R f
  disjoint f h
  disjoint T f
  disjoint W f
  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T ) -> { g e. ( T X. E ) | E. s e. E g = <. ( s ` F ) , .0. >. } = { g e. ( T X. E ) | ( ( R ` ( 1st ` g ) ) .<_ ( R ` F ) /\ ( 2nd ` g ) = .0. ) } )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cF
    cT
    wcel
    wa
    #
    vg
    cv
    #
    cF
    vs
    cv
    cfv
    #
    c.0
    cop
    wceq
    #
    vs
    cE
    wrex
    #
    @1
    c1st
    cfv
    #
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
    @1
    c2nd
    cfv
    c.0
    wceq
    #
    wa
    #
    vg
    cT
    cE
    cxp
    #
    @0
    @1
    @11
    wcel
    #
    wa
    #
    @4
    @5
    @2
    wceq
    #
    @9
    wa
    #
    vs
    cE
    wrex
    #
    @10
    @13
    @3
    @15
    vs
    cE
    @12
    @3
    @15
    wb
    @0
    @1
    @2
    c.0
    cT
    cE
    eqop
    adantl
    rexbidv
    @16
    @14
    vs
    cE
    wrex
    #
    @9
    wa
    @13
    @10
    @14
    @9
    vs
    cE
    r19.41v
    @13
    @17
    @8
    @9
    @13
    @17
    @5
    vf
    cv
    #
    cR
    cfv
    #
    @7
    c.le
    wbr
    #
    vf
    cT
    crab
    #
    wcel
    #
    @8
    @17
    @5
    @18
    @2
    wceq
    #
    vs
    cE
    wrex
    #
    vf
    cab
    #
    wcel
    @13
    @22
    @24
    @17
    vf
    @5
    @1
    c1st
    fvex
    @18
    @5
    wceq
    #
    @23
    @14
    vs
    cE
    @18
    @5
    @2
    eqeq1
    rexbidv
    elab
    @13
    @25
    @21
    @5
    @0
    @25
    @21
    wceq
    @12
    cR
    cT
    vf
    cE
    cF
    cH
    cK
    c.le
    cW
    vs
    dvhb1dim.l
    dvhb1dim.h
    dvhb1dim.t
    dvhb1dim.r
    dvhb1dim.e
    dva1dim
    adantr
    eleq2d
    syl5bbr
    @13
    @5
    cT
    wcel
    #
    @22
    @8
    wb
    @12
    @27
    @0
    @1
    cT
    cE
    xp1st
    adantl
    @20
    @8
    vf
    @5
    cT
    @26
    @19
    @6
    @7
    c.le
    @18
    @5
    cR
    fveq2
    breq1d
    elrab3
    syl
    bitrd
    anbi1d
    syl5bb
    bitrd
    rabbidva
end
