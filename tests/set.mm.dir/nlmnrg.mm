include "cnlm.mm"
include "wcel.mm"
include "cngp.mm"
include "clmod.mm"
include "cnrg.mm"
include "w3a.mm"
include "cv.mm"
include "cvsca.mm"
include "cfv.mm"
include "co.mm"
include "cnm.mm"
include "cmul.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "eqid.mm"
include "isnlm.mm"
include "simplbi.mm"
include "simp3d.mm"

theorem nlmnrg
  let cF: class F
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume nlmnrg.1: |- F = ( Scalar ` W )


  assert |- ( W e. NrmMod -> F e. NrmRing )

  proof
    cW
    cnlm
    wcel
    #
    cW
    cngp
    wcel
    #
    cW
    clmod
    wcel
    #
    cF
    cnrg
    wcel
    #
    @0
    @1
    @2
    @3
    w3a
    vx
    cv
    #
    vy
    cv
    #
    cW
    cvsca
    cfv
    #
    co
    cW
    cnm
    cfv
    #
    cfv
    @4
    cF
    cnm
    cfv
    #
    cfv
    @5
    @7
    cfv
    cmul
    co
    wceq
    vy
    cW
    cbs
    cfv
    #
    wral
    vx
    cF
    cbs
    cfv
    #
    wral
    vx
    vy
    @8
    @6
    cF
    @10
    @7
    @9
    cW
    @9
    eqid
    @7
    eqid
    @6
    eqid
    nlmnrg.1
    @10
    eqid
    @8
    eqid
    isnlm
    simplbi
    simp3d
end
