include "ax-5.mm"

theorem ax5ALT
  let wph: wff ph
  let vx: setvar x

  disjoint ph x
  assert |- ( ph -> A. x ph )

  proof
    wph
    vx
    ax-5
end
