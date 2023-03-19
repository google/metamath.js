include "wcel.mm"
include "wa.mm"
include "csca.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cltrn.mm"
include "cop.mm"
include "cplusg.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt2.mm"
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
include "cedring.mm"
include "fvex.mm"
include "eqeltri.mm"
include "lmodsca.mm"
include "ax-mp.mm"
include "3eqtr4g.mm"

theorem dvasca
  let cD: class D
  let cU: class U
  let cF: class F
  let cH: class H
  let cK: class K
  let cW: class W
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vs: setvar s
  assume dvasca.h: |- H = ( LHyp ` K )
  assume dvasca.d: |- D = ( ( EDRing ` K ) ` W )
  assume dvasca.u: |- U = ( ( DVecA ` K ) ` W )
  assume dvasca.f: |- F = ( Scalar ` U )


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
    vg
    cv
    ccom
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
    cW
    cK
    ctendo
    cfv
    cfv
    #
    @1
    @2
    vs
    cv
    cfv
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
    @6
    csca
    cD
    @1
    cU
    vf
    vg
    @4
    cH
    cK
    cW
    cX
    vs
    dvasca.h
    @1
    eqid
    @4
    eqid
    dvasca.d
    dvasca.u
    dvaset
    fveq2d
    dvasca.f
    cD
    cvv
    wcel
    cD
    @7
    wceq
    cD
    cW
    cK
    cedring
    cfv
    #
    cfv
    cvv
    dvasca.d
    cW
    @8
    fvex
    eqeltri
    @1
    @3
    @5
    cD
    @6
    cvv
    @6
    eqid
    lmodsca
    ax-mp
    3eqtr4g
end
