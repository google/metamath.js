include "abeqin.mm"
include "rabimbieq.mm"

theorem abeqinbi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume abeqinbi.1: |- A = ( B i^i C )
  assume abeqinbi.2: |- B = { x | ph }
  assume abeqinbi.3: |- ( x e. C -> ( ph <-> ps ) )

  disjoint C x
  assert |- A = { x e. C | ps }

  proof
    wph
    wps
    vx
    cC
    cA
    wph
    vx
    cA
    cB
    cC
    abeqinbi.1
    abeqinbi.2
    abeqin
    abeqinbi.3
    rabimbieq
end
