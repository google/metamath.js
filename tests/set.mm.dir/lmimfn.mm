include "clmod.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "wf1o.mm"
include "clmhm.mm"
include "co.mm"
include "crab.mm"
include "clmim.mm"
include "df-lmim.mm"
include "ovex.mm"
include "rabex.mm"
include "fnmpt2i.mm"

theorem lmimfn
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


  assert |- LMIso Fn ( LMod X. LMod )

  proof
    vs
    vt
    clmod
    clmod
    vs
    cv
    #
    cbs
    cfv
    vt
    cv
    #
    cbs
    cfv
    vg
    cv
    wf1o
    #
    vg
    @0
    @1
    clmhm
    co
    #
    crab
    clmim
    vt
    vg
    vs
    df-lmim
    @2
    vg
    @3
    @0
    @1
    clmhm
    ovex
    rabex
    fnmpt2i
end
