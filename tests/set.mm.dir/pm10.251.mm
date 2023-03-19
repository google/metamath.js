include "wn.mm"
include "wal.mm"
include "wex.mm"
include "alnex.mm"
include "19.2.mm"
include "con3i.mm"
include "sylbi.mm"

theorem pm10.251
  let wph: wff ph
  let vx: setvar x


  assert |- ( A. x -. ph -> -. A. x ph )

  proof
    wph
    wn
    vx
    wal
    wph
    vx
    wex
    #
    wn
    wph
    vx
    wal
    #
    wn
    wph
    vx
    alnex
    @1
    @0
    wph
    vx
    19.2
    con3i
    sylbi
end
