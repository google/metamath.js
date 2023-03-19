include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cop.mm"
include "co.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "ccom.mm"
include "cxp.mm"
include "wceq.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "dvhvsca.mm"
include "syl12anc.mm"
include "op1stg.mm"
include "fveq2d.mm"
include "op2ndg.mm"
include "coeq2d.mm"
include "opeq12d.mm"
include "eqtrd.mm"

theorem dvhopvsca
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
  let cX: class X
  let vf: setvar f
  let vs: setvar s
  let vg: setvar g
  let vh: setvar h
  assume dvhfvsca.h: |- H = ( LHyp ` K )
  assume dvhfvsca.t: |- T = ( ( LTrn ` K ) ` W )
  assume dvhfvsca.e: |- E = ( ( TEndo ` K ) ` W )
  assume dvhfvsca.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvhfvsca.s: |- .x. = ( .s ` U )


  assert |- ( ( ( K e. V /\ W e. H ) /\ ( R e. E /\ F e. T /\ X e. E ) ) -> ( R .x. <. F , X >. ) = <. ( R ` F ) , ( R o. X ) >. )

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
    #
    cF
    cT
    wcel
    #
    cX
    cE
    wcel
    #
    w3a
    #
    wa
    #
    cR
    cF
    cX
    cop
    #
    c.x
    co
    #
    @6
    c1st
    cfv
    #
    cR
    cfv
    #
    cR
    @6
    c2nd
    cfv
    #
    ccom
    #
    cop
    #
    cF
    cR
    cfv
    #
    cR
    cX
    ccom
    #
    cop
    @5
    @0
    @1
    @6
    cT
    cE
    cxp
    wcel
    #
    @7
    @12
    wceq
    @0
    @4
    simpl
    @0
    @1
    @2
    @3
    simpr1
    @5
    @2
    @3
    @15
    @0
    @1
    @2
    @3
    simpr2
    #
    @0
    @1
    @2
    @3
    simpr3
    #
    cF
    cX
    cT
    cE
    opelxpi
    syl2anc
    cR
    cT
    c.x
    cU
    cE
    @6
    cH
    cK
    cV
    cW
    dvhfvsca.h
    dvhfvsca.t
    dvhfvsca.e
    dvhfvsca.u
    dvhfvsca.s
    dvhvsca
    syl12anc
    @5
    @9
    @13
    @11
    @14
    @5
    @8
    cF
    cR
    @5
    @2
    @3
    @8
    cF
    wceq
    @16
    @17
    cF
    cX
    cT
    cE
    op1stg
    syl2anc
    fveq2d
    @5
    @10
    cX
    cR
    @5
    @2
    @3
    @10
    cX
    wceq
    @16
    @17
    cF
    cX
    cT
    cE
    op2ndg
    syl2anc
    coeq2d
    opeq12d
    eqtrd
end
