include "wal.mm"
include "19.3v.mm"
include "biimpi.mm"

theorem spvw
  let wph: wff ph
  let vx: setvar x

  disjoint ph x
  assert |- ( A. x ph -> ph )

  proof
    wph
    vx
    wal
    wph
    wph
    vx
    19.3v
    biimpi
end
