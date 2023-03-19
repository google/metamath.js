include "cnlm.mm"
include "wcel.mm"
include "cngp.mm"
include "clmod.mm"
include "csca.mm"
include "cfv.mm"
include "cnrg.mm"
include "w3a.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "cnm.mm"
include "cmul.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "eqid.mm"
include "isnlm.mm"
include "simplbi.mm"
include "simp2d.mm"

theorem nlmlmod
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let cF: class F


  assert |- ( W e. NrmMod -> W e. LMod )

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
    cW
    csca
    cfv
    #
    cnrg
    wcel
    #
    @0
    @1
    @2
    @4
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
    @5
    @3
    cnm
    cfv
    #
    cfv
    @6
    @8
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
    @3
    cbs
    cfv
    #
    wral
    vx
    vy
    @9
    @7
    @3
    @11
    @8
    @10
    cW
    @10
    eqid
    @8
    eqid
    @7
    eqid
    @3
    eqid
    @11
    eqid
    @9
    eqid
    isnlm
    simplbi
    simp2d
end
