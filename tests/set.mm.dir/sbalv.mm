include "wal.mm"
include "wsb.mm"
include "sbal.mm"
include "albii.mm"
include "bitri.mm"

theorem sbalv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume sbalv.1: |- ( [ y / x ] ph <-> ps )

  disjoint x z
  disjoint y z
  assert |- ( [ y / x ] A. z ph <-> A. z ps )

  proof
    wph
    vz
    wal
    vx
    vy
    wsb
    wph
    vx
    vy
    wsb
    #
    vz
    wal
    wps
    vz
    wal
    wph
    vz
    vx
    vy
    sbal
    @0
    wps
    vz
    sbalv.1
    albii
    bitri
end
