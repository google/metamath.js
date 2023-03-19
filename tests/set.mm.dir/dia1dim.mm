include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "crab.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cbs.mm"
include "simpl.mm"
include "eqid.mm"
include "trlcl.mm"
include "trlle.mm"
include "diaval.mm"
include "syl12anc.mm"
include "dva1dim.mm"
include "eqtr4d.mm"

theorem dia1dim
  let cR: class R
  let cT: class T
  let vg: setvar g
  let cE: class E
  let cF: class F
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let vs: setvar s
  assume dia1dim.h: |- H = ( LHyp ` K )
  assume dia1dim.t: |- T = ( ( LTrn ` K ) ` W )
  assume dia1dim.r: |- R = ( ( trL ` K ) ` W )
  assume dia1dim.e: |- E = ( ( TEndo ` K ) ` W )
  assume dia1dim.i: |- I = ( ( DIsoA ` K ) ` W )

  disjoint E s
  disjoint g s
  disjoint F g
  disjoint F s
  disjoint H g
  disjoint H s
  disjoint K g
  disjoint K s
  disjoint R g
  disjoint R s
  disjoint T g
  disjoint T s
  disjoint W g
  disjoint W s
  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T ) -> ( I ` ( R ` F ) ) = { g | E. s e. E g = ( s ` F ) } )

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
    cF
    cR
    cfv
    #
    cI
    cfv
    #
    vg
    cv
    #
    cR
    cfv
    @3
    cK
    cple
    cfv
    #
    wbr
    vg
    cT
    crab
    #
    @5
    cF
    vs
    cv
    cfv
    wceq
    vs
    cE
    wrex
    vg
    cab
    @2
    @0
    @3
    cK
    cbs
    cfv
    #
    wcel
    @3
    cW
    @6
    wbr
    @4
    @7
    wceq
    @0
    @1
    simpl
    @8
    cR
    cT
    cF
    cH
    cK
    cW
    @8
    eqid
    #
    dia1dim.h
    dia1dim.t
    dia1dim.r
    trlcl
    cR
    cT
    cF
    cH
    cK
    @6
    cW
    @6
    eqid
    #
    dia1dim.h
    dia1dim.t
    dia1dim.r
    trlle
    @8
    cR
    cT
    vg
    cH
    cI
    cK
    @6
    chlt
    cW
    @3
    @9
    @10
    dia1dim.h
    dia1dim.t
    dia1dim.r
    dia1dim.i
    diaval
    syl12anc
    cR
    cT
    vg
    cE
    cF
    cH
    cK
    @6
    cW
    vs
    @10
    dia1dim.h
    dia1dim.t
    dia1dim.r
    dia1dim.e
    dva1dim
    eqtr4d
end
