include "wo.mm"
include "oridm.mm"
include "2exbii.mm"

theorem pm11.7
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( E. x E. y ( ph \/ ph ) <-> E. x E. y ph )

  proof
    wph
    wph
    wo
    wph
    vx
    vy
    wph
    oridm
    2exbii
end
