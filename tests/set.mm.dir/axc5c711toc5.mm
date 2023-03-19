include "wal.mm"
include "wn.mm"
include "wi.mm"
include "ax-1.mm"
include "axc5c711.mm"
include "syl.mm"

theorem axc5c711toc5
  let wph: wff ph
  let vx: setvar x


  assert |- ( A. x ph -> ph )

  proof
    wph
    vx
    wal
    #
    @0
    vx
    wal
    wn
    vx
    wal
    vx
    wal
    #
    @0
    wi
    wph
    @0
    @1
    ax-1
    wph
    vx
    vx
    axc5c711
    syl
end
