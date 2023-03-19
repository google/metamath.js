include "crab.mm"
include "nfrab1.mm"
include "nfcxfr.mm"
include "nfcrii.mm"

theorem bnj1230
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume bnj1230.1: |- B = { x e. A | ph }

  disjoint x y
  assert |- ( y e. B -> A. x y e. B )

  proof
    vx
    vy
    cB
    vx
    cB
    wph
    vx
    cA
    crab
    bnj1230.1
    wph
    vx
    cA
    nfrab1
    nfcxfr
    nfcrii
end
