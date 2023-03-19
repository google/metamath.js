include "wal.mm"
include "wn.mm"
include "wex.mm"
include "19.2.mm"
include "df-ex.mm"
include "sylib.mm"
include "con2i.mm"

theorem bj-modald
  let wph: wff ph
  let vx: setvar x


  assert |- ( A. x -. ph -> -. A. x ph )

  proof
    wph
    vx
    wal
    #
    wph
    wn
    vx
    wal
    #
    @0
    wph
    vx
    wex
    @1
    wn
    wph
    vx
    19.2
    wph
    vx
    df-ex
    sylib
    con2i
end
