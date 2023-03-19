include "wal.mm"
include "ax-gen.mm"
include "mpbir.mm"

theorem mpgbir
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume mpgbir.1: |- ( ph <-> A. x ps )
  assume mpgbir.2: |- ps


  assert |- ph

  proof
    wph
    wps
    vx
    wal
    wps
    vx
    mpgbir.2
    ax-gen
    mpgbir.1
    mpbir
end
