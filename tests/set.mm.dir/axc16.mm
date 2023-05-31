include "axc16g.mm"

theorem axc16
  param wph: wff ph
  param vx: setvar x
  param vy: setvar y

  disjoint x y
  assert |- ( A. x x = y -> ( ph -> A. x ph ) )

  proof
    wph
    vx
    vy
    vx
    axc16g
end
