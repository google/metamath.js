include "ssrab3.mm"
include "cv.mm"
include "wcel.mm"
include "simp2bi.mm"
include "bnj1213.mm"

theorem bnj1212
  let wph: wff ph
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume bnj1212.1: |- B = { x e. A | ph }
  assume bnj1212.2: |- ( th <-> ( ch /\ x e. B /\ ta ) )

  disjoint A x
  assert |- ( th -> x e. A )

  proof
    wth
    vx
    cB
    cA
    wph
    vx
    cA
    cB
    bnj1212.1
    ssrab3
    wth
    wch
    vx
    cv
    cB
    wcel
    wta
    bnj1212.2
    simp2bi
    bnj1213
end
