include "sp.mm"

theorem axc5
  let wph: wff ph
  let vx: setvar x


  assert |- ( A. x ph -> ph )

  proof
    wph
    vx
    sp
end
