include "wex.mm"
include "19.8a.mm"
include "con3i.mm"

theorem bj-nexrt
  let wph: wff ph
  let vx: setvar x


  assert |- ( -. E. x ph -> -. ph )

  proof
    wph
    wph
    vx
    wex
    wph
    vx
    19.8a
    con3i
end
