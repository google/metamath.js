include "cfn.mm"
include "wcel.mm"
include "wfo.mm"
include "cdom.mm"
include "wbr.mm"
include "fodomfi.mm"
include "domfi.mm"
include "syldan.mm"

theorem fofi
  let cA: class A
  let cB: class B
  let cF: class F
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. Fin /\ F : A -onto-> B ) -> B e. Fin )

  proof
    cA
    cfn
    wcel
    cA
    cB
    cF
    wfo
    cB
    cA
    cdom
    wbr
    cB
    cfn
    wcel
    cA
    cB
    cF
    fodomfi
    cA
    cB
    domfi
    syldan
end
