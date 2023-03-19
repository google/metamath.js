include "wal.mm"
include "ax-gen.mm"
include "ax-mp.mm"

theorem mpg
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume mpg.1: |- ( A. x ph -> ps )
  assume mpg.2: |- ph


  assert |- ps

  proof
    wph
    vx
    wal
    wps
    wph
    vx
    mpg.2
    ax-gen
    mpg.1
    ax-mp
end
