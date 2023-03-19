include "wn.mm"
include "wex.mm"
include "wal.mm"
include "exnal.mm"
include "albii.mm"
include "alnex.mm"
include "bitri.mm"

theorem alexn
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x E. y -. ph <-> -. E. x A. y ph )

  proof
    wph
    wn
    vy
    wex
    #
    vx
    wal
    wph
    vy
    wal
    #
    wn
    #
    vx
    wal
    @1
    vx
    wex
    wn
    @0
    @2
    vx
    wph
    vy
    exnal
    albii
    @1
    vx
    alnex
    bitri
end
