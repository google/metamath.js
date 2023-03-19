include "weq.mm"
include "wal.mm"
include "hbae.mm"
include "exbidh.mm"

theorem drex2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume dral1.1: |- ( A. x x = y -> ( ph <-> ps ) )


  assert |- ( A. x x = y -> ( E. z ph <-> E. z ps ) )

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
    hbae
    dral1.1
    exbidh
end
