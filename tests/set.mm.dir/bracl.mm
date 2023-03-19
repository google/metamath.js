include "chil.mm"
include "wcel.mm"
include "cc.mm"
include "cbr.mm"
include "cfv.mm"
include "brafn.mm"
include "ffvelrnda.mm"

theorem bracl
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cS: class S
  let cT: class T


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( ( bra ` A ) ` B ) e. CC )

  proof
    cA
    chil
    wcel
    chil
    cc
    cB
    cA
    cbr
    cfv
    cA
    brafn
    ffvelrnda
end
