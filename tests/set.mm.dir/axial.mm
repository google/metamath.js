include "hba1.mm"

theorem axial
  let wph: wff ph
  let vx: setvar x


  assert |- ( A. x ph -> A. x A. x ph )

  proof
    wph
    vx
    hba1
end
