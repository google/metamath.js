include "wal.mm"
include "simpli.mm"
include "ax-gen.mm"
include "simpri.mm"
include "pm3.2i.mm"

theorem bj-genl
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume bj-genr.1: |- ( ph /\ ps )


  assert |- ( A. x ph /\ ps )

  proof
    wph
    vx
    wal
    wps
    wph
    vx
    wph
    wps
    bj-genr.1
    simpli
    ax-gen
    wph
    wps
    bj-genr.1
    simpri
    pm3.2i
end
