include "wal.mm"
include "id.mm"

theorem ax11dgen
  let wph: wff ph
  let vx: setvar x


  assert |- ( A. x A. x ph -> A. x A. x ph )

  proof
    wph
    vx
    wal
    vx
    wal
    id
end
