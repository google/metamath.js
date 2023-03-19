include "wal.mm"
include "ax-c5.mm"
include "syl.mm"

theorem sps-o
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume sps-o.1: |- ( ph -> ps )


  assert |- ( A. x ph -> ps )

  proof
    wph
    vx
    wal
    wph
    wps
    wph
    vx
    ax-c5
    sps-o.1
    syl
end
