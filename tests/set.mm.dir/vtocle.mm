include "cvv.mm"
include "wcel.mm"
include "vtocleg.mm"
include "ax-mp.mm"

theorem vtocle
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assume vtocle.1: |- A e. _V
  assume vtocle.2: |- ( x = A -> ph )

  disjoint A x
  disjoint ph x
  assert |- ph

  proof
    cA
    cvv
    wcel
    wph
    vtocle.1
    wph
    vx
    cA
    cvv
    vtocle.2
    vtocleg
    ax-mp
end
