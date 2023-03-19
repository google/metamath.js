include "wcel.mm"
include "wa.mm"
include "cplusg.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt2.mm"
include "csca.mm"
include "cedring.mm"
include "ctp.mm"
include "cvsca.mm"
include "ctendo.mm"
include "csn.mm"
include "cun.mm"
include "eqid.mm"
include "dvaset.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wceq.mm"
include "cltrn.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mpt2ex.mm"
include "lmodplusg.mm"
include "ax-mp.mm"
include "3eqtr4g.mm"

theorem dvafvadd
  let c.pl: class .+
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  let cK: class K
  let cW: class W
  let cX: class X
  let vs: setvar s
  assume dvafvadd.h: |- H = ( LHyp ` K )
  assume dvafvadd.t: |- T = ( ( LTrn ` K ) ` W )
  assume dvafvadd.u: |- U = ( ( DVecA ` K ) ` W )
  assume dvafvadd.v: |- .+ = ( +g ` U )

  disjoint f g
  disjoint K f
  disjoint K g
  disjoint T f
  disjoint T g
  disjoint W f
  disjoint W g
  disjoint f s
  disjoint g s
  disjoint K s
  disjoint W s
  assert |- ( ( K e. X /\ W e. H ) -> .+ = ( f e. T , g e. T |-> ( f o. g ) ) )

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
    cplusg
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
    #
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
    cW
    cK
    ctendo
    cfv
    cfv
    #
    cT
    @1
    vs
    cv
    cfv
    cmpt2
    #
    cop
    csn
    cun
    #
    cplusg
    cfv
    #
    c.pl
    @3
    @0
    cU
    @7
    cplusg
    @4
    cT
    cU
    vf
    vg
    @5
    cH
    cK
    cW
    cX
    vs
    dvafvadd.h
    dvafvadd.t
    @5
    eqid
    @4
    eqid
    dvafvadd.u
    dvaset
    fveq2d
    dvafvadd.v
    @3
    cvv
    wcel
    @3
    @8
    wceq
    vf
    vg
    cT
    cT
    @2
    cT
    cW
    cK
    cltrn
    cfv
    #
    cfv
    cvv
    dvafvadd.t
    cW
    @9
    fvex
    eqeltri
    #
    @10
    mpt2ex
    cT
    @3
    @6
    @4
    @7
    cvv
    @7
    eqid
    lmodplusg
    ax-mp
    3eqtr4g
end
