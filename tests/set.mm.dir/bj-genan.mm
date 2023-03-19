include "wal.mm"
include "simpli.mm"
include "ax-gen.mm"
include "simpri.mm"
include "pm3.2i.mm"

theorem bj-genan
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume bj-genr.1: |- ( ph /\ ps )


  assert |- ( A. x ph /\ A. x ps )

  proof
    wph
    vx
    wal
    wps
    vx
    wal
    wph
    vx
    wph
    wps
    bj-genr.1
    simpli
    ax-gen
    wps
    vx
    wph
    wps
    bj-genr.1
    simpri
    ax-gen
    pm3.2i
end
