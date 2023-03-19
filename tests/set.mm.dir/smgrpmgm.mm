include "csem.mm"
include "wcel.mm"
include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "issmgrpOLD.mm"
include "simpl.mm"
include "syl6bi.mm"
include "pm2.43i.mm"

theorem smgrpmgm
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume smgrpmgm.1: |- X = dom dom G


  assert |- ( G e. SemiGrp -> G : ( X X. X ) --> X )

  proof
    cG
    csem
    wcel
    #
    cX
    cX
    cxp
    cX
    cG
    wf
    #
    @0
    @0
    @1
    vx
    cv
    #
    vy
    cv
    #
    cG
    co
    vz
    cv
    #
    cG
    co
    @2
    @3
    @4
    cG
    co
    cG
    co
    wceq
    vz
    cX
    wral
    vy
    cX
    wral
    vx
    cX
    wral
    #
    wa
    @1
    vx
    vy
    vz
    csem
    cG
    cX
    smgrpmgm.1
    issmgrpOLD
    @1
    @5
    simpl
    syl6bi
    pm2.43i
end
