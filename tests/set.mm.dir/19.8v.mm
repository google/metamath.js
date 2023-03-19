include "ax-5.mm"
include "19.8w.mm"

theorem 19.8v
  let wph: wff ph
  let vx: setvar x

  disjoint ph x
  assert |- ( ph -> E. x ph )

  proof
    wph
    vx
    wph
    vx
    ax-5
    19.8w
end
