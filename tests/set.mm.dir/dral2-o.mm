include "weq.mm"
include "wal.mm"
include "hbae-o.mm"
include "albidh.mm"

theorem dral2-o
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume dral2-o.1: |- ( A. x x = y -> ( ph <-> ps ) )


  assert |- ( A. x x = y -> ( A. z ph <-> A. z ps ) )

  proof
    vx
    vy
    weq
    vx
    wal
    wph
    wps
    vz
    vx
    vy
    vz
    hbae-o
    dral2-o.1
    albidh
end
