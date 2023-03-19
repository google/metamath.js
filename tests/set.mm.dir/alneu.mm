include "weu.mm"
include "wal.mm"
include "wn.mm"
include "wex.mm"
include "eunex.mm"
include "exnal.mm"
include "sylib.mm"
include "con2i.mm"

theorem alneu
  let wph: wff ph
  let vx: setvar x
  let vk: setvar k


  assert |- ( A. x ph -> -. E! x ph )

  proof
    wph
    vx
    weu
    #
    wph
    vx
    wal
    #
    @0
    wph
    wn
    vx
    wex
    @1
    wn
    wph
    vx
    eunex
    wph
    vx
    exnal
    sylib
    con2i
end
