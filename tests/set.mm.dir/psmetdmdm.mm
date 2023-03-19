include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "cdm.mm"
include "cxp.mm"
include "cxr.mm"
include "wf.mm"
include "wceq.mm"
include "cv.mm"
include "co.mm"
include "cc0.mm"
include "cxad.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "cvv.mm"
include "elfvex.mm"
include "ispsmet.mm"
include "biimpa.mm"
include "mpancom.mm"
include "simpld.mm"
include "fdm.mm"
include "dmeqd.mm"
include "syl.mm"
include "dmxpid.mm"
include "syl6req.mm"

theorem psmetdmdm
  let cD: class D
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( D e. ( PsMet ` X ) -> X = dom dom D )

  proof
    cD
    cX
    cpsmet
    cfv
    wcel
    #
    cD
    cdm
    #
    cdm
    #
    cX
    cX
    cxp
    #
    cdm
    #
    cX
    @0
    @3
    cxr
    cD
    wf
    #
    @2
    @4
    wceq
    @0
    @5
    vx
    cv
    #
    @6
    cD
    co
    cc0
    wceq
    @6
    vy
    cv
    #
    cD
    co
    vz
    cv
    #
    @6
    cD
    co
    @8
    @7
    cD
    co
    cxad
    co
    cle
    wbr
    vz
    cX
    wral
    vy
    cX
    wral
    wa
    vx
    cX
    wral
    #
    cX
    cvv
    wcel
    #
    @0
    @5
    @9
    wa
    #
    cD
    cX
    cpsmet
    elfvex
    @10
    @0
    @11
    vx
    vy
    vz
    cD
    cvv
    cX
    ispsmet
    biimpa
    mpancom
    simpld
    @5
    @1
    @3
    @3
    cxr
    cD
    fdm
    dmeqd
    syl
    cX
    dmxpid
    syl6req
end
