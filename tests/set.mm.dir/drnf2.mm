include "weq.mm"
include "wal.mm"
include "nfae.mm"
include "nfbidf.mm"

theorem drnf2
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z
  assume dral1.1: |- ( A. x x = y -> ( ph <-> ps ) )


  assert |- ( A. x x = y -> ( F/ z ph <-> F/ z ps ) )

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
    nfbidf
end
