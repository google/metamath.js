include "csem.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cxp.mm"
include "wf.mm"
include "wa.mm"
include "issmgrpOLD.mm"
include "simpr.mm"
include "syl6bi.mm"
include "pm2.43i.mm"

theorem smgrpassOLD
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cG: class G
  let cX: class X
  assume smgrpassOLD.1: |- X = dom dom G

  disjoint G x
  disjoint G y
  disjoint G z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( G e. SemiGrp -> A. x e. X A. y e. X A. z e. X ( ( x G y ) G z ) = ( x G ( y G z ) ) )

  proof
    cG
    csem
    wcel
    #
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
    @1
    @2
    @3
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
    @0
    @0
    cX
    cX
    cxp
    cX
    cG
    wf
    #
    @4
    wa
    @4
    vx
    vy
    vz
    csem
    cG
    cX
    smgrpassOLD.1
    issmgrpOLD
    @5
    @4
    simpr
    syl6bi
    pm2.43i
end
