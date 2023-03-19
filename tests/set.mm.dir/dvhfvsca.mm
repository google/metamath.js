include "wcel.mm"
include "wa.mm"
include "cvsca.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
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
include "csn.mm"
include "cun.mm"
include "eqid.mm"
include "dvhset.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wceq.mm"
include "ctendo.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cltrn.mm"
include "xpex.mm"
include "mpt2ex.mm"
include "lmodvsca.mm"
include "ax-mp.mm"
include "3eqtr4g.mm"

theorem dvhfvsca
  let cT: class T
  let c.x: class .x.
  let cU: class U
  let vf: setvar f
  let cE: class E
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vg: setvar g
  let vh: setvar h
  assume dvhfvsca.h: |- H = ( LHyp ` K )
  assume dvhfvsca.t: |- T = ( ( LTrn ` K ) ` W )
  assume dvhfvsca.e: |- E = ( ( TEndo ` K ) ` W )
  assume dvhfvsca.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvhfvsca.s: |- .x. = ( .s ` U )

  disjoint f s
  disjoint E f
  disjoint E s
  disjoint H f
  disjoint K f
  disjoint K s
  disjoint T f
  disjoint T s
  disjoint V f
  disjoint W f
  disjoint W s
  disjoint f g
  disjoint H g
  disjoint f h
  disjoint g h
  disjoint g s
  disjoint K g
  disjoint h s
  disjoint K h
  disjoint T h
  disjoint V g
  disjoint W g
  disjoint W h
  assert |- ( ( K e. V /\ W e. H ) -> .x. = ( s e. E , f e. ( T X. E ) |-> <. ( s ` ( 1st ` f ) ) , ( s o. ( 2nd ` f ) ) >. ) )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    #
    cU
    cvsca
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
    #
    cmpt2
    #
    cop
    csn
    cun
    #
    cvsca
    cfv
    #
    c.x
    @11
    @0
    cU
    @12
    cvsca
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
    cV
    vs
    dvhfvsca.h
    dvhfvsca.t
    dvhfvsca.e
    @8
    eqid
    dvhfvsca.u
    dvhset
    fveq2d
    dvhfvsca.s
    @11
    cvv
    wcel
    @11
    @13
    wceq
    vs
    vf
    cE
    @1
    @10
    cE
    cW
    cK
    ctendo
    cfv
    #
    cfv
    cvv
    dvhfvsca.e
    cW
    @14
    fvex
    eqeltri
    #
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
    dvhfvsca.t
    cW
    @16
    fvex
    eqeltri
    @15
    xpex
    mpt2ex
    @1
    @7
    @11
    @8
    @12
    cvv
    @12
    eqid
    lmodvsca
    ax-mp
    3eqtr4g
end
