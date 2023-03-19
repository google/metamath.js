include "wal.mm"
include "wn.mm"
include "wex.mm"
include "alex.mm"
include "con2bii.mm"

theorem exnal
  let wph: wff ph
  let vx: setvar x


  assert |- ( E. x -. ph <-> -. A. x ph )

  proof
    wph
    vx
    wal
    wph
    wn
    vx
    wex
    wph
    vx
    alex
    con2bii
end
