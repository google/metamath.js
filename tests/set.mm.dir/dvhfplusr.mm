include "wcel.mm"
include "wa.mm"
include "cplusg.mm"
include "cfv.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "cedring.mm"
include "eqid.mm"
include "dvhsca.mm"
include "fveq2d.mm"
include "erngfplus.mm"
include "eqtrd.mm"
include "3eqtr4g.mm"

theorem dvhfplusr
  let vt: setvar t
  let c.pl: class .+
  let c.pb: class .+b
  let cT: class T
  let cU: class U
  let vf: setvar f
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vs: setvar s
  assume dvhfplusr.h: |- H = ( LHyp ` K )
  assume dvhfplusr.t: |- T = ( ( LTrn ` K ) ` W )
  assume dvhfplusr.e: |- E = ( ( TEndo ` K ) ` W )
  assume dvhfplusr.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvhfplusr.f: |- F = ( Scalar ` U )
  assume dvhfplusr.p: |- .+ = ( s e. E , t e. E |-> ( f e. T |-> ( ( s ` f ) o. ( t ` f ) ) ) )
  assume dvhfplusr.s: |- .+b = ( +g ` F )

  disjoint s t
  disjoint E s
  disjoint E t
  disjoint H f
  disjoint f s
  disjoint f t
  disjoint K f
  disjoint K s
  disjoint K t
  disjoint V f
  disjoint W f
  disjoint W s
  disjoint W t
  assert |- ( ( K e. V /\ W e. H ) -> .+b = .+ )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    #
    cF
    cplusg
    cfv
    #
    vs
    vt
    cE
    cE
    vf
    cT
    vf
    cv
    #
    vs
    cv
    cfv
    @2
    vt
    cv
    cfv
    ccom
    cmpt
    cmpt2
    #
    c.pb
    c.pl
    @0
    @1
    cW
    cK
    cedring
    cfv
    cfv
    #
    cplusg
    cfv
    #
    @3
    @0
    cF
    @4
    cplusg
    @4
    cU
    cF
    cH
    cK
    cW
    cV
    dvhfplusr.h
    @4
    eqid
    #
    dvhfplusr.u
    dvhfplusr.f
    dvhsca
    fveq2d
    vt
    @4
    @5
    cT
    vf
    cE
    cH
    cK
    cV
    cW
    vs
    dvhfplusr.h
    dvhfplusr.t
    dvhfplusr.e
    @6
    @5
    eqid
    erngfplus
    eqtrd
    dvhfplusr.s
    dvhfplusr.p
    3eqtr4g
end
