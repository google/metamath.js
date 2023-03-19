include "wal.mm"
include "wsb.mm"
include "stdpc4.mm"
include "anim12i.mm"

theorem pm10.14
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A. x ph /\ A. x ps ) -> ( [ y / x ] ph /\ [ y / x ] ps ) )

  proof
    wph
    vx
    wal
    wph
    vx
    vy
    wsb
    wps
    vx
    wal
    wps
    vx
    vy
    wsb
    wph
    vx
    vy
    stdpc4
    wps
    vx
    vy
    stdpc4
    anim12i
end
