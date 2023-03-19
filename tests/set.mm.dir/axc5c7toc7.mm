include "wal.mm"
include "wn.mm"
include "wi.mm"
include "pm2.21.mm"
include "axc5c7.mm"
include "syl.mm"

theorem axc5c7toc7
  let wph: wff ph
  let vx: setvar x


  assert |- ( -. A. x -. A. x ph -> ph )

  proof
    wph
    vx
    wal
    #
    wn
    vx
    wal
    #
    wn
    @1
    @0
    wi
    wph
    @1
    @0
    pm2.21
    wph
    vx
    axc5c7
    syl
end
