include "casa.mm"
include "wcel.mm"
include "clmod.mm"
include "crg.mm"
include "ccrg.mm"
include "w3a.mm"
include "cv.mm"
include "cvsca.mm"
include "cfv.mm"
include "co.mm"
include "cmulr.mm"
include "wceq.mm"
include "wa.mm"
include "cbs.mm"
include "wral.mm"
include "eqid.mm"
include "isassa.mm"
include "simplbi.mm"
include "simp3d.mm"

theorem assasca
  let cF: class F
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume assasca.f: |- F = ( Scalar ` W )


  assert |- ( W e. AssAlg -> F e. CRing )

  proof
    cW
    casa
    wcel
    #
    cW
    clmod
    wcel
    #
    cW
    crg
    wcel
    #
    cF
    ccrg
    wcel
    #
    @0
    @1
    @2
    @3
    w3a
    vz
    cv
    #
    vx
    cv
    #
    cW
    cvsca
    cfv
    #
    co
    vy
    cv
    #
    cW
    cmulr
    cfv
    #
    co
    @4
    @5
    @7
    @8
    co
    @6
    co
    #
    wceq
    @5
    @4
    @7
    @6
    co
    @8
    co
    @9
    wceq
    wa
    vy
    cW
    cbs
    cfv
    #
    wral
    vx
    @10
    wral
    vz
    cF
    cbs
    cfv
    #
    wral
    vx
    vy
    @11
    @6
    @8
    cF
    @10
    cW
    vz
    @10
    eqid
    assasca.f
    @11
    eqid
    @6
    eqid
    @8
    eqid
    isassa
    simplbi
    simp3d
end
