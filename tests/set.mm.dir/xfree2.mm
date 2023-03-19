include "wal.mm"
include "wi.mm"
include "wex.mm"
include "wn.mm"
include "xfree.mm"
include "eximal.mm"
include "albii.mm"
include "bitri.mm"

theorem xfree2
  let wph: wff ph
  let vx: setvar x


  assert |- ( A. x ( ph -> A. x ph ) <-> A. x ( -. ph -> A. x -. ph ) )

  proof
    wph
    wph
    vx
    wal
    wi
    vx
    wal
    wph
    vx
    wex
    wph
    wi
    #
    vx
    wal
    wph
    wn
    #
    @1
    vx
    wal
    wi
    #
    vx
    wal
    wph
    vx
    xfree
    @0
    @2
    vx
    wph
    wph
    vx
    eximal
    albii
    bitri
end
