include "wal.mm"
include "ax-gen.mm"
include "a1i.mm"

theorem hbth
  let wph: wff ph
  let vx: setvar x
  assume hbth.1: |- ph


  assert |- ( ph -> A. x ph )

  proof
    wph
    vx
    wal
    wph
    wph
    vx
    hbth.1
    ax-gen
    a1i
end
