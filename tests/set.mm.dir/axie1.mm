include "hbe1.mm"

theorem axie1
  let wph: wff ph
  let vx: setvar x


  assert |- ( E. x ph -> A. x E. x ph )

  proof
    wph
    vx
    hbe1
end
