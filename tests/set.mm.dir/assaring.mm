include "casa.mm"
include "wcel.mm"
include "clmod.mm"
include "crg.mm"
include "csca.mm"
include "cfv.mm"
include "ccrg.mm"
include "w3a.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "cmulr.mm"
include "wceq.mm"
include "wa.mm"
include "cbs.mm"
include "wral.mm"
include "eqid.mm"
include "isassa.mm"
include "simplbi.mm"
include "simp2d.mm"

theorem assaring
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F


  assert |- ( W e. AssAlg -> W e. Ring )

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
    cW
    csca
    cfv
    #
    ccrg
    wcel
    #
    @0
    @1
    @2
    @4
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
    @5
    @6
    @8
    @9
    co
    @7
    co
    #
    wceq
    @6
    @5
    @8
    @7
    co
    @9
    co
    @10
    wceq
    wa
    vy
    cW
    cbs
    cfv
    #
    wral
    vx
    @11
    wral
    vz
    @3
    cbs
    cfv
    #
    wral
    vx
    vy
    @12
    @7
    @9
    @3
    @11
    cW
    vz
    @11
    eqid
    @3
    eqid
    @12
    eqid
    @7
    eqid
    @9
    eqid
    isassa
    simplbi
    simp2d
end
