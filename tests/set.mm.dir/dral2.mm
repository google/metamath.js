include "weq.mm"
include "wal.mm"
include "nfae.mm"
include "albid.mm"

theorem dral2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume dral1.1: |- ( A. x x = y -> ( ph <-> ps ) )


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
    nfae
    dral1.1
    albid
end
