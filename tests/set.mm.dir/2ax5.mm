include "id.mm"
include "alrimivv.mm"

theorem 2ax5
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint ph x
  disjoint ph y
  assert |- ( ph -> A. x A. y ph )

  proof
    wph
    wph
    vx
    vy
    wph
    id
    alrimivv
end
