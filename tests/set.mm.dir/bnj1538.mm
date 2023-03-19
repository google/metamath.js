include "cv.mm"
include "wcel.mm"
include "rabeq2i.mm"
include "simprbi.mm"

theorem bnj1538
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume bnj1538.1: |- A = { x e. B | ph }


  assert |- ( x e. A -> ph )

  proof
    vx
    cv
    #
    cA
    wcel
    @0
    cB
    wcel
    wph
    wph
    vx
    cA
    cB
    bnj1538.1
    rabeq2i
    simprbi
end
