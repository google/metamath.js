include "wal.mm"
include "wn.mm"
include "wi.mm"
include "hba1-o.mm"
include "con3i.mm"
include "alimi.mm"
include "sps-o.mm"
include "pm2.21.mm"
include "axc5c711.mm"
include "3syl.mm"

theorem axc5c711toc7
  let wph: wff ph
  let vx: setvar x


  assert |- ( -. A. x -. A. x ph -> ph )

  proof
    wph
    vx
    wal
    #
    wn
    #
    vx
    wal
    #
    wn
    @0
    vx
    wal
    #
    wn
    #
    vx
    wal
    #
    vx
    wal
    #
    wn
    @6
    @0
    wi
    wph
    @6
    @2
    @5
    @2
    vx
    @4
    @1
    vx
    @0
    @3
    wph
    vx
    hba1-o
    con3i
    alimi
    sps-o
    con3i
    @6
    @0
    pm2.21
    wph
    vx
    vx
    axc5c711
    3syl
end
