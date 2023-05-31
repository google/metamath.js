include "wal.mm"
include "wn.mm"
include "wex.mm"
include "notnotb.mm"
include "albii.mm"
include "alnex.mm"
include "bitri.mm"

theorem alex
  param wph: wff ph
  param vx: setvar x


  assert |- ( A. x ph <-> -. E. x -. ph )

  proof
    wph
    vx
    wal
    wph
    wn
    #
    wn
    #
    vx
    wal
    @0
    vx
    wex
    wn
    wph
    @1
    vx
    wph
    notnotb
    albii
    @0
    vx
    alnex
    bitri
end
