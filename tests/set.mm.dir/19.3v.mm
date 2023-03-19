include "wal.mm"
include "wn.mm"
include "wex.mm"
include "alex.mm"
include "19.9v.mm"
include "con2bii.mm"
include "bitr4i.mm"

theorem 19.3v
  let wph: wff ph
  let vx: setvar x

  disjoint ph x
  assert |- ( A. x ph <-> ph )

  proof
    wph
    vx
    wal
    wph
    wn
    #
    vx
    wex
    #
    wn
    wph
    wph
    vx
    alex
    @1
    wph
    @0
    vx
    19.9v
    con2bii
    bitr4i
end
