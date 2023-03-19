include "axc16g.mm"

theorem axc16
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( A. x x = y -> ( ph -> A. x ph ) )

  proof
    wph
    vx
    vy
    vx
    axc16g
end
