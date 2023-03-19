include "stdpc4.mm"

theorem axfrege58b
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x ph -> [ y / x ] ph )

  proof
    wph
    vx
    vy
    stdpc4
end
