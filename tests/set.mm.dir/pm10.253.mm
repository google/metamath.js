include "wn.mm"
include "wex.mm"
include "wal.mm"
include "alex.mm"
include "bicomi.mm"
include "con1bii.mm"

theorem pm10.253
  let wph: wff ph
  let vx: setvar x


  assert |- ( -. A. x ph <-> E. x -. ph )

  proof
    wph
    wn
    vx
    wex
    #
    wph
    vx
    wal
    #
    @1
    @0
    wn
    wph
    vx
    alex
    bicomi
    con1bii
end
