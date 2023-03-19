include "wi.mm"
include "wal.mm"
include "alim.mm"
include "al2imi.mm"

theorem bj-2alim
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x A. y ( ph -> ps ) -> ( A. x A. y ph -> A. x A. y ps ) )

  proof
    wph
    wps
    wi
    vy
    wal
    wph
    vy
    wal
    wps
    vy
    wal
    vx
    wph
    wps
    vy
    alim
    al2imi
end
