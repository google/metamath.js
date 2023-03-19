include "wal.mm"
include "ax-gen.mm"
include "mpbi.mm"

theorem mpgbi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume mpgbi.1: |- ( A. x ph <-> ps )
  assume mpgbi.2: |- ph


  assert |- ps

  proof
    wph
    vx
    wal
    wps
    wph
    vx
    mpgbi.2
    ax-gen
    mpgbi.1
    mpbi
end
