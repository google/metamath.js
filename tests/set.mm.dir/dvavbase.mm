include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cnx.mm"
include "cop.mm"
include "cplusg.mm"
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
include "lmodbase.mm"
include "ax-mp.mm"
include "3eqtr4g.mm"

theorem dvavbase
  let cT: class T
  let cU: class U
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vs: setvar s
  assume dvavbase.h: |- H = ( LHyp ` K )
  assume dvavbase.t: |- T = ( ( LTrn ` K ) ` W )
  assume dvavbase.u: |- U = ( ( DVecA ` K ) ` W )
  assume dvavbase.v: |- V = ( Base ` U )


  assert |- ( ( K e. X /\ W e. H ) -> V = T )

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
    cbs
    cfv
    #
    cV
    cT
    @0
    cU
    @6
    cbs
    @3
    cT
    cU
    vf
    vg
    @4
    cH
    cK
    cW
    cX
    vs
    dvavbase.h
    dvavbase.t
    @4
    eqid
    @3
    eqid
    dvavbase.u
    dvaset
    fveq2d
    dvavbase.v
    cT
    cvv
    wcel
    cT
    @7
    wceq
    cT
    cW
    cK
    cltrn
    cfv
    #
    cfv
    cvv
    dvavbase.t
    cW
    @8
    fvex
    eqeltri
    cT
    @2
    @5
    @3
    @6
    cvv
    @6
    eqid
    lmodbase
    ax-mp
    3eqtr4g
end
