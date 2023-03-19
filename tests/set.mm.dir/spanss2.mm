include "chil.mm"
include "wss.mm"
include "cv.mm"
include "csh.mm"
include "crab.mm"
include "cint.mm"
include "cspn.mm"
include "cfv.mm"
include "ssintub.mm"
include "spanval.mm"
include "syl5sseqr.mm"

theorem spanss2
  let cA: class A
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( A C_ ~H -> A C_ ( span ` A ) )

  proof
    cA
    chil
    wss
    cA
    vx
    cv
    wss
    vx
    csh
    crab
    cint
    cA
    cA
    cspn
    cfv
    vx
    cA
    csh
    ssintub
    vx
    cA
    spanval
    syl5sseqr
end
