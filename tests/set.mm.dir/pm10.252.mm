include "wn.mm"
include "wal.mm"
include "wex.mm"
include "df-ex.mm"
include "bicomi.mm"
include "con1bii.mm"

theorem pm10.252
  let wph: wff ph
  let vx: setvar x


  assert |- ( -. E. x ph <-> A. x -. ph )

  proof
    wph
    wn
    vx
    wal
    #
    wph
    vx
    wex
    #
    @1
    @0
    wn
    wph
    vx
    df-ex
    bicomi
    con1bii
end
