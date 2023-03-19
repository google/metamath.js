include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "co.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "ccom.mm"
include "cop.mm"
include "dvhvsca.mm"
include "simpl.mm"
include "simprl.mm"
include "xp1st.mm"
include "ad2antll.mm"
include "tendocl.mm"
include "syl3anc.mm"
include "xp2nd.mm"
include "tendococl.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "eqeltrd.mm"

theorem dvhvscacl
  let cR: class R
  let cT: class T
  let c.x: class .x.
  let cU: class U
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let cW: class W
  let vf: setvar f
  let vs: setvar s
  let vg: setvar g
  let vh: setvar h
  let cV: class V
  assume dvhfvsca.h: |- H = ( LHyp ` K )
  assume dvhfvsca.t: |- T = ( ( LTrn ` K ) ` W )
  assume dvhfvsca.e: |- E = ( ( TEndo ` K ) ` W )
  assume dvhfvsca.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvhfvsca.s: |- .x. = ( .s ` U )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( R e. E /\ F e. ( T X. E ) ) ) -> ( R .x. F ) e. ( T X. E ) )

  proof
    cK
    chlt
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
    cE
    cxp
    #
    wcel
    #
    wa
    #
    wa
    #
    cR
    cF
    c.x
    co
    cF
    c1st
    cfv
    #
    cR
    cfv
    #
    cR
    cF
    c2nd
    cfv
    #
    ccom
    #
    cop
    #
    @2
    cR
    cT
    c.x
    cU
    cE
    cF
    cH
    cK
    chlt
    cW
    dvhfvsca.h
    dvhfvsca.t
    dvhfvsca.e
    dvhfvsca.u
    dvhfvsca.s
    dvhvsca
    @5
    @7
    cT
    wcel
    #
    @9
    cE
    wcel
    #
    @10
    @2
    wcel
    @5
    @0
    @1
    @6
    cT
    wcel
    #
    @11
    @0
    @4
    simpl
    #
    @0
    @1
    @3
    simprl
    #
    @3
    @13
    @0
    @1
    cF
    cT
    cE
    xp1st
    ad2antll
    cR
    cT
    cE
    @6
    cH
    cK
    chlt
    cW
    dvhfvsca.h
    dvhfvsca.t
    dvhfvsca.e
    tendocl
    syl3anc
    @5
    @0
    @1
    @8
    cE
    wcel
    #
    @12
    @14
    @15
    @3
    @16
    @0
    @1
    cF
    cT
    cE
    xp2nd
    ad2antll
    cR
    @8
    cE
    cH
    cK
    cW
    dvhfvsca.h
    dvhfvsca.e
    tendococl
    syl3anc
    @7
    @9
    cT
    cE
    opelxpi
    syl2anc
    eqeltrd
end
