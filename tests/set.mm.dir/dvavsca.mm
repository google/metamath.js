include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt2.mm"
include "dvafvsca.mm"
include "oveqd.mm"
include "fveq1.mm"
include "fveq2.mm"
include "eqid.mm"
include "fvex.mm"
include "ovmpt2.mm"
include "sylan9eq.mm"

theorem dvavsca
  let cR: class R
  let cT: class T
  let c.x: class .x.
  let cU: class U
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vs: setvar s
  let vg: setvar g
  assume dvafvsca.h: |- H = ( LHyp ` K )
  assume dvafvsca.t: |- T = ( ( LTrn ` K ) ` W )
  assume dvafvsca.e: |- E = ( ( TEndo ` K ) ` W )
  assume dvafvsca.u: |- U = ( ( DVecA ` K ) ` W )
  assume dvafvsca.s: |- .x. = ( .s ` U )


  assert |- ( ( ( K e. V /\ W e. H ) /\ ( R e. E /\ F e. T ) ) -> ( R .x. F ) = ( R ` F ) )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    #
    cR
    cE
    wcel
    cF
    cT
    wcel
    wa
    cR
    cF
    c.x
    co
    cR
    cF
    vs
    vf
    cE
    cT
    vf
    cv
    #
    vs
    cv
    #
    cfv
    #
    cmpt2
    #
    co
    cF
    cR
    cfv
    #
    @0
    c.x
    @4
    cR
    cF
    cT
    c.x
    cU
    vf
    cE
    cH
    cK
    cV
    cW
    vs
    dvafvsca.h
    dvafvsca.t
    dvafvsca.e
    dvafvsca.u
    dvafvsca.s
    dvafvsca
    oveqd
    vs
    vf
    cR
    cF
    cE
    cT
    @3
    @5
    @4
    @1
    cR
    cfv
    @1
    @2
    cR
    fveq1
    @1
    cF
    cR
    fveq2
    @4
    eqid
    cF
    cR
    fvex
    ovmpt2
    sylan9eq
end
