include "wsb.mm"
include "wal.mm"
include "sb9.mm"
include "biimpi.mm"

theorem sb9i
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x [ x / y ] ph -> A. y [ y / x ] ph )

  proof
    wph
    vy
    vx
    wsb
    vx
    wal
    wph
    vx
    vy
    wsb
    vy
    wal
    wph
    vx
    vy
    sb9
    biimpi
end
