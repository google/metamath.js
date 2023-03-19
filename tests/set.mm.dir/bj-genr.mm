include "wal.mm"
include "simpli.mm"
include "simpri.mm"
include "ax-gen.mm"
include "pm3.2i.mm"

theorem bj-genr
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume bj-genr.1: |- ( ph /\ ps )


  assert |- ( ph /\ A. x ps )

  proof
    wph
    wps
    vx
    wal
    wph
    wps
    bj-genr.1
    simpli
    wps
    vx
    wph
    wps
    bj-genr.1
    simpri
    ax-gen
    pm3.2i
end
