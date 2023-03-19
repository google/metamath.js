include "wal.mm"
include "wn.mm"
include "wi.mm"
include "ax-1.mm"
include "axc5c7.mm"
include "syl.mm"

theorem axc5c7toc5
  let wph: wff ph
  let vx: setvar x


  assert |- ( A. x ph -> ph )

  proof
    wph
    vx
    wal
    #
    @0
    wn
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
    axc5c7
    syl
end
