include "19.2d.mm"

theorem 19.8w
  let wph: wff ph
  let vx: setvar x
  assume 19.8w.1: |- ( ph -> A. x ph )


  assert |- ( ph -> E. x ph )

  proof
    wph
    wph
    vx
    19.8w.1
    19.2d
end
