include "clmod.mm"
include "cv.mm"
include "csca.mm"
include "cfv.mm"
include "wceq.mm"
include "cvsca.mm"
include "co.mm"
include "cbs.mm"
include "wral.mm"
include "wa.mm"
include "wsbc.mm"
include "cghm.mm"
include "crab.mm"
include "clmhm.mm"
include "df-lmhm.mm"
include "reldmmpt2.mm"

theorem reldmlmhm
  let vf: setvar f
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let vx: setvar x
  let cB: class B
  let vy: setvar y
  let cE: class E
  let cK: class K
  let cS: class S
  let cF: class F
  let vg: setvar g
  let cT: class T
  let c.x: class .x.
  let c.xp: class .X.
  let cL: class L


  assert |- Rel dom LMHom

  proof
    vs
    vt
    clmod
    clmod
    vt
    cv
    #
    csca
    cfv
    vw
    cv
    #
    wceq
    vx
    cv
    #
    vy
    cv
    #
    vs
    cv
    #
    cvsca
    cfv
    co
    vf
    cv
    #
    cfv
    @2
    @3
    @5
    cfv
    @0
    cvsca
    cfv
    co
    wceq
    vy
    @4
    cbs
    cfv
    wral
    vx
    @1
    cbs
    cfv
    wral
    wa
    vw
    @4
    csca
    cfv
    wsbc
    vf
    @4
    @0
    cghm
    co
    crab
    clmhm
    vx
    vy
    vw
    vt
    vf
    vs
    df-lmhm
    reldmmpt2
end
