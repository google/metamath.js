include "wi.mm"
include "id.mm"
include "2al2imi.mm"

theorem 2alim
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x A. y ( ph -> ps ) -> ( A. x A. y ph -> A. x A. y ps ) )

  proof
    wph
    wps
    wi
    #
    wph
    wps
    vx
    vy
    @0
    id
    2al2imi
end
