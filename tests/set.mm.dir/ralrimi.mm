include "nf5ri.mm"
include "hbralrimi.mm"

theorem ralrimi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume ralrimi.1: |- F/ x ph
  assume ralrimi.2: |- ( ph -> ( x e. A -> ps ) )


  assert |- ( ph -> A. x e. A ps )

  proof
    wph
    wps
    vx
    cA
    wph
    vx
    ralrimi.1
    nf5ri
    ralrimi.2
    hbralrimi
end
