include "cgr.mm"
include "wcel.mm"
include "cmndo.mm"
include "crn.mm"
include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "w3a.mm"
include "eqid.mm"
include "isgrpo.mm"
include "biimpd.mm"
include "wi.mm"
include "grpoidinv.mm"
include "simpl.mm"
include "ralimi.mm"
include "reximi.mm"
include "ismndo2.mm"
include "biimprcd.mm"
include "3exp.mm"
include "impcom.mm"
include "com3l.mm"
include "syl.mm"
include "mpcom.mm"
include "expdcom.mm"
include "a1i.mm"
include "com13.mm"
include "3imp.mm"
include "syli.mm"
include "pm2.43i.mm"

theorem grpomndo
  let cG: class G
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( G e. GrpOp -> G e. MndOp )

  proof
    cG
    cgr
    wcel
    #
    cG
    cmndo
    wcel
    #
    @0
    @0
    cG
    crn
    #
    @2
    cxp
    @2
    cG
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    co
    #
    vz
    cv
    #
    cG
    co
    @4
    @5
    @7
    cG
    co
    cG
    co
    wceq
    vz
    @2
    wral
    vy
    @2
    wral
    vx
    @2
    wral
    #
    vw
    cv
    #
    @4
    cG
    co
    @4
    wceq
    @5
    @4
    cG
    co
    #
    @9
    wceq
    vy
    @2
    wrex
    wa
    vx
    @2
    wral
    vw
    @2
    wrex
    #
    w3a
    #
    @1
    @0
    @0
    @12
    vx
    vy
    vz
    vw
    cgr
    cG
    @2
    @2
    eqid
    #
    isgrpo
    biimpd
    @3
    @8
    @11
    @0
    @1
    wi
    #
    @11
    @8
    @3
    @14
    @8
    @3
    @14
    wi
    wi
    @11
    @0
    @8
    @3
    @1
    @6
    @5
    wceq
    @10
    @5
    wceq
    wa
    #
    @9
    @5
    cG
    co
    @4
    wceq
    @5
    @9
    cG
    co
    @4
    wceq
    wa
    vw
    @2
    wrex
    #
    wa
    #
    vy
    @2
    wral
    #
    vx
    @2
    wrex
    #
    @0
    @8
    @3
    wa
    #
    @1
    wi
    #
    vy
    vw
    vx
    cG
    @2
    @13
    grpoidinv
    @19
    @15
    vy
    @2
    wral
    #
    vx
    @2
    wrex
    #
    @0
    @21
    wi
    @18
    @22
    vx
    @2
    @17
    @15
    vy
    @2
    @15
    @16
    simpl
    ralimi
    reximi
    @20
    @23
    @0
    @1
    @3
    @8
    @23
    @14
    wi
    @3
    @8
    @23
    @14
    @0
    @1
    @3
    @8
    @23
    w3a
    vx
    vy
    vz
    cgr
    cG
    @2
    @13
    ismndo2
    biimprcd
    3exp
    impcom
    com3l
    syl
    mpcom
    expdcom
    a1i
    com13
    3imp
    syli
    pm2.43i
end
