include "wcel.mm"
include "wa.mm"
include "csca.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cltrn.mm"
include "ctendo.mm"
include "cxp.mm"
include "cop.mm"
include "cplusg.mm"
include "cv.mm"
include "c1st.mm"
include "ccom.mm"
include "c2nd.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "ctp.mm"
include "cvsca.mm"
include "csn.mm"
include "cun.mm"
include "eqid.mm"
include "dvhset.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wceq.mm"
include "cedring.mm"
include "fvex.mm"
include "eqeltri.mm"
include "lmodsca.mm"
include "ax-mp.mm"
include "3eqtr4g.mm"

theorem dvhsca
  let cD: class D
  let cU: class U
  let cF: class F
  let cH: class H
  let cK: class K
  let cW: class W
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vs: setvar s
  assume dvhsca.h: |- H = ( LHyp ` K )
  assume dvhsca.d: |- D = ( ( EDRing ` K ) ` W )
  assume dvhsca.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvhsca.f: |- F = ( Scalar ` U )


  assert |- ( ( K e. X /\ W e. H ) -> F = D )

  proof
    cK
    cX
    wcel
    cW
    cH
    wcel
    wa
    #
    cU
    csca
    cfv
    cnx
    cbs
    cfv
    cW
    cK
    cltrn
    cfv
    cfv
    #
    cW
    cK
    ctendo
    cfv
    cfv
    #
    cxp
    #
    cop
    cnx
    cplusg
    cfv
    vf
    vg
    @3
    @3
    vf
    cv
    #
    c1st
    cfv
    #
    vg
    cv
    #
    c1st
    cfv
    ccom
    vh
    @1
    vh
    cv
    #
    @4
    c2nd
    cfv
    #
    cfv
    @7
    @6
    c2nd
    cfv
    cfv
    ccom
    cmpt
    cop
    cmpt2
    #
    cop
    cnx
    csca
    cfv
    cD
    cop
    ctp
    cnx
    cvsca
    cfv
    vs
    vf
    @2
    @3
    @5
    vs
    cv
    #
    cfv
    @10
    @8
    ccom
    cop
    cmpt2
    #
    cop
    csn
    cun
    #
    csca
    cfv
    #
    cF
    cD
    @0
    cU
    @12
    csca
    cD
    @1
    cU
    vf
    vg
    vh
    @2
    cH
    cK
    cW
    cX
    vs
    dvhsca.h
    @1
    eqid
    @2
    eqid
    dvhsca.d
    dvhsca.u
    dvhset
    fveq2d
    dvhsca.f
    cD
    cvv
    wcel
    cD
    @13
    wceq
    cD
    cW
    cK
    cedring
    cfv
    #
    cfv
    cvv
    dvhsca.d
    cW
    @14
    fvex
    eqeltri
    @3
    @9
    @11
    cD
    @12
    cvv
    @12
    eqid
    lmodsca
    ax-mp
    3eqtr4g
end
