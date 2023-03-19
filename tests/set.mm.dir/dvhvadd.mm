include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "co.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "ccom.mm"
include "c2nd.mm"
include "cop.mm"
include "cmpt2.mm"
include "eqid.mm"
include "dvhfvadd.mm"
include "oveqd.mm"
include "dvhvaddval.mm"
include "sylan9eq.mm"

theorem dvhvadd
  let cD: class D
  let c.pl: class .+
  let c.pd: class .+^
  let cT: class T
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let vf: setvar f
  let vg: setvar g
  assume dvhvadd.h: |- H = ( LHyp ` K )
  assume dvhvadd.t: |- T = ( ( LTrn ` K ) ` W )
  assume dvhvadd.e: |- E = ( ( TEndo ` K ) ` W )
  assume dvhvadd.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvhvadd.f: |- D = ( Scalar ` U )
  assume dvhvadd.s: |- .+ = ( +g ` U )
  assume dvhvadd.p: |- .+^ = ( +g ` D )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. ( T X. E ) /\ G e. ( T X. E ) ) ) -> ( F .+ G ) = <. ( ( 1st ` F ) o. ( 1st ` G ) ) , ( ( 2nd ` F ) .+^ ( 2nd ` G ) ) >. )

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
    cE
    cxp
    #
    wcel
    cG
    @1
    wcel
    wa
    cF
    cG
    c.pl
    co
    cF
    cG
    vf
    vg
    @1
    @1
    vf
    cv
    #
    c1st
    cfv
    vg
    cv
    #
    c1st
    cfv
    ccom
    @2
    c2nd
    cfv
    @3
    c2nd
    cfv
    c.pd
    co
    cop
    cmpt2
    #
    co
    cF
    c1st
    cfv
    cG
    c1st
    cfv
    ccom
    cF
    c2nd
    cfv
    cG
    c2nd
    cfv
    c.pd
    co
    cop
    @0
    c.pl
    @4
    cF
    cG
    cD
    c.pl
    c.pd
    @4
    cT
    cU
    vf
    vg
    cE
    cH
    cK
    cW
    dvhvadd.h
    dvhvadd.t
    dvhvadd.e
    dvhvadd.u
    dvhvadd.f
    dvhvadd.p
    @4
    eqid
    #
    dvhvadd.s
    dvhfvadd
    oveqd
    @4
    c.pd
    cT
    vf
    vg
    cE
    cF
    cG
    @5
    dvhvaddval
    sylan9eq
end
