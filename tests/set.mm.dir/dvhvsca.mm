include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "co.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "ccom.mm"
include "cop.mm"
include "cmpt2.mm"
include "dvhfvsca.mm"
include "oveqd.mm"
include "eqid.mm"
include "dvhvscaval.mm"
include "sylan9eq.mm"

theorem dvhvsca
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
  let vh: setvar h
  assume dvhfvsca.h: |- H = ( LHyp ` K )
  assume dvhfvsca.t: |- T = ( ( LTrn ` K ) ` W )
  assume dvhfvsca.e: |- E = ( ( TEndo ` K ) ` W )
  assume dvhfvsca.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvhfvsca.s: |- .x. = ( .s ` U )


  assert |- ( ( ( K e. V /\ W e. H ) /\ ( R e. E /\ F e. ( T X. E ) ) ) -> ( R .x. F ) = <. ( R ` ( 1st ` F ) ) , ( R o. ( 2nd ` F ) ) >. )

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
    cE
    cxp
    #
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
    @1
    vf
    cv
    #
    c1st
    cfv
    vs
    cv
    #
    cfv
    @3
    @2
    c2nd
    cfv
    ccom
    cop
    cmpt2
    #
    co
    cF
    c1st
    cfv
    cR
    cfv
    cR
    cF
    c2nd
    cfv
    ccom
    cop
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
    dvhfvsca.h
    dvhfvsca.t
    dvhfvsca.e
    dvhfvsca.u
    dvhfvsca.s
    dvhfvsca
    oveqd
    cT
    @4
    cR
    vf
    cE
    cF
    vs
    @4
    eqid
    dvhvscaval
    sylan9eq
end
