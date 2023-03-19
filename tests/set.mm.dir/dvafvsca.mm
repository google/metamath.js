include "wcel.mm"
include "wa.mm"
include "cvsca.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cplusg.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt2.mm"
include "csca.mm"
include "cedring.mm"
include "ctp.mm"
include "csn.mm"
include "cun.mm"
include "eqid.mm"
include "dvaset.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wceq.mm"
include "ctendo.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cltrn.mm"
include "mpt2ex.mm"
include "lmodvsca.mm"
include "ax-mp.mm"
include "3eqtr4g.mm"

theorem dvafvsca
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
  assume dvafvsca.h: |- H = ( LHyp ` K )
  assume dvafvsca.t: |- T = ( ( LTrn ` K ) ` W )
  assume dvafvsca.e: |- E = ( ( TEndo ` K ) ` W )
  assume dvafvsca.u: |- U = ( ( DVecA ` K ) ` W )
  assume dvafvsca.s: |- .x. = ( .s ` U )

  disjoint f s
  disjoint E f
  disjoint E s
  disjoint K f
  disjoint K s
  disjoint T f
  disjoint T s
  disjoint W f
  disjoint W s
  disjoint f g
  disjoint g s
  disjoint K g
  disjoint W g
  assert |- ( ( K e. V /\ W e. H ) -> .x. = ( s e. E , f e. T |-> ( s ` f ) ) )

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
    cop
    cnx
    cplusg
    cfv
    vf
    vg
    cT
    cT
    vf
    cv
    #
    vg
    cv
    ccom
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
    cT
    @1
    vs
    cv
    cfv
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
    @5
    @0
    cU
    @6
    cvsca
    @3
    cT
    cU
    vf
    vg
    cE
    cH
    cK
    cW
    cV
    vs
    dvafvsca.h
    dvafvsca.t
    dvafvsca.e
    @3
    eqid
    dvafvsca.u
    dvaset
    fveq2d
    dvafvsca.s
    @5
    cvv
    wcel
    @5
    @7
    wceq
    vs
    vf
    cE
    cT
    @4
    cE
    cW
    cK
    ctendo
    cfv
    #
    cfv
    cvv
    dvafvsca.e
    cW
    @8
    fvex
    eqeltri
    cT
    cW
    cK
    cltrn
    cfv
    #
    cfv
    cvv
    dvafvsca.t
    cW
    @9
    fvex
    eqeltri
    mpt2ex
    cT
    @2
    @5
    @3
    @6
    cvv
    @6
    eqid
    lmodvsca
    ax-mp
    3eqtr4g
end
