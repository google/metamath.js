include "wi.mm"
include "wal.mm"
include "wex.mm"
include "exim.mm"
include "aleximi.mm"

theorem bj-2exim
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x A. y ( ph -> ps ) -> ( E. x E. y ph -> E. x E. y ps ) )

  proof
    wph
    wps
    wi
    vy
    wal
    wph
    vy
    wex
    wps
    vy
    wex
    vx
    wph
    wps
    vy
    exim
    aleximi
end
