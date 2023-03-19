include "wal.mm"
include "19.8a.mm"
include "19.35ri.mm"

theorem qexmid
  let wph: wff ph
  let vx: setvar x


  assert |- E. x ( ph -> A. x ph )

  proof
    wph
    wph
    vx
    wal
    #
    vx
    @0
    vx
    19.8a
    19.35ri
end
