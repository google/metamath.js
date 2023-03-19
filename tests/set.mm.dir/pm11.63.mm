include "wex.mm"
include "wn.mm"
include "wal.mm"
include "wi.mm"
include "2nexaln.mm"
include "pm2.21.mm"
include "2alimi.mm"
include "sylbi.mm"

theorem pm11.63
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( -. E. x E. y ph -> A. x A. y ( ph -> ps ) )

  proof
    wph
    vy
    wex
    vx
    wex
    wn
    wph
    wn
    #
    vy
    wal
    vx
    wal
    wph
    wps
    wi
    #
    vy
    wal
    vx
    wal
    wph
    vx
    vy
    2nexaln
    @0
    @1
    vx
    vy
    wph
    wps
    pm2.21
    2alimi
    sylbi
end
