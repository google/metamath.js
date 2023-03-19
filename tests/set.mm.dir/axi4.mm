include "sp.mm"

theorem axi4
  let wph: wff ph
  let vx: setvar x


  assert |- ( A. x ph -> ph )

  proof
    wph
    vx
    sp
end
