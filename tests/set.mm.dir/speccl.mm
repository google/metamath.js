include "chil.mm"
include "wf.mm"
include "cspc.mm"
include "cfv.mm"
include "cv.mm"
include "cid.mm"
include "cres.mm"
include "chot.mm"
include "co.mm"
include "chod.mm"
include "wf1.mm"
include "wn.mm"
include "cc.mm"
include "crab.mm"
include "specval.mm"
include "ssrab2.mm"
include "syl6eqss.mm"

theorem speccl
  let cT: class T
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( T : ~H --> ~H -> ( Lambda ` T ) C_ CC )

  proof
    chil
    chil
    cT
    wf
    cT
    cspc
    cfv
    chil
    chil
    cT
    vx
    cv
    cid
    chil
    cres
    chot
    co
    chod
    co
    wf1
    wn
    #
    vx
    cc
    crab
    cc
    vx
    cT
    specval
    @0
    vx
    cc
    ssrab2
    syl6eqss
end
