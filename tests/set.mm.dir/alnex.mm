include "wex.mm"
include "wn.mm"
include "wal.mm"
include "df-ex.mm"
include "con2bii.mm"

theorem alnex
  param wph: wff ph
  param vx: setvar x


  assert |- ( A. x -. ph <-> -. E. x ph )

  proof
    wph
    vx
    wex
    wph
    wn
    vx
    wal
    wph
    vx
    df-ex
    con2bii
end
