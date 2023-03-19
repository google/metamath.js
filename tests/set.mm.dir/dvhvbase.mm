include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cnx.mm"
include "cxp.mm"
include "cop.mm"
include "cplusg.mm"
include "cv.mm"
include "c1st.mm"
include "ccom.mm"
include "c2nd.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "csca.mm"
include "cedring.mm"
include "ctp.mm"
include "cvsca.mm"
include "csn.mm"
include "cun.mm"
include "eqid.mm"
include "dvhset.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wceq.mm"
include "cltrn.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ctendo.mm"
include "xpex.mm"
include "lmodbase.mm"
include "ax-mp.mm"
include "3eqtr4g.mm"

theorem dvhvbase
  let cT: class T
  let cU: class U
  let cE: class E
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vs: setvar s
  assume dvhvbase.h: |- H = ( LHyp ` K )
  assume dvhvbase.t: |- T = ( ( LTrn ` K ) ` W )
  assume dvhvbase.e: |- E = ( ( TEndo ` K ) ` W )
  assume dvhvbase.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvhvbase.v: |- V = ( Base ` U )


  assert |- ( ( K e. X /\ W e. H ) -> V = ( T X. E ) )

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
    cbs
    cfv
    cnx
    cbs
    cfv
    cT
    cE
    cxp
    #
    cop
    cnx
    cplusg
    cfv
    vf
    vg
    @1
    @1
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
    cT
    vh
    cv
    #
    @2
    c2nd
    cfv
    #
    cfv
    @5
    @4
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
    cW
    cK
    cedring
    cfv
    cfv
    #
    cop
    ctp
    cnx
    cvsca
    cfv
    vs
    vf
    cE
    @1
    @3
    vs
    cv
    #
    cfv
    @9
    @6
    ccom
    cop
    cmpt2
    #
    cop
    csn
    cun
    #
    cbs
    cfv
    #
    cV
    @1
    @0
    cU
    @11
    cbs
    @8
    cT
    cU
    vf
    vg
    vh
    cE
    cH
    cK
    cW
    cX
    vs
    dvhvbase.h
    dvhvbase.t
    dvhvbase.e
    @8
    eqid
    dvhvbase.u
    dvhset
    fveq2d
    dvhvbase.v
    @1
    cvv
    wcel
    @1
    @12
    wceq
    cT
    cE
    cT
    cW
    cK
    cltrn
    cfv
    #
    cfv
    cvv
    dvhvbase.t
    cW
    @13
    fvex
    eqeltri
    cE
    cW
    cK
    ctendo
    cfv
    #
    cfv
    cvv
    dvhvbase.e
    cW
    @14
    fvex
    eqeltri
    xpex
    @1
    @7
    @10
    @8
    @11
    cvv
    @11
    eqid
    lmodbase
    ax-mp
    3eqtr4g
end
