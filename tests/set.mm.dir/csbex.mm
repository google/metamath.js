include "cvv.mm"
include "wcel.mm"
include "csb.mm"
include "csbexg.mm"
include "mpg.mm"

theorem csbex
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume csbex.1: |- B e. _V


  assert |- [_ A / x ]_ B e. _V

  proof
    cB
    cvv
    wcel
    vx
    cA
    cB
    csb
    cvv
    wcel
    vx
    vx
    cA
    cB
    cvv
    csbexg
    csbex.1
    mpg
end
