include "wal.mm"
include "albii.mm"
include "3imtr4i.mm"

theorem hbxfrbi
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  assume hbxfrbi.1: |- ( ph <-> ps )
  assume hbxfrbi.2: |- ( ps -> A. x ps )


  assert |- ( ph -> A. x ph )

  proof
    wps
    wps
    vx
    wal
    wph
    wph
    vx
    wal
    hbxfrbi.2
    hbxfrbi.1
    wph
    wps
    vx
    hbxfrbi.1
    albii
    3imtr4i
end
