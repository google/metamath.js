include "ax-5.mm"
include "hbralrimi.mm"

theorem ralrimiv
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  param cA: class A
  assume ralrimiv.1: |- ( ph -> ( x e. A -> ps ) )

  disjoint ph x
  assert |- ( ph -> A. x e. A ps )

  proof
    wph
    wps
    vx
    cA
    wph
    vx
    ax-5
    ralrimiv.1
    hbralrimi
end
