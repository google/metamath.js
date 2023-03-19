include "wal.mm"
include "wn.mm"
include "axc5c711toc7.mm"
include "con4i.mm"
include "wi.mm"
include "pm2.21.mm"
include "axc5c711.mm"
include "syl.mm"
include "alimi.mm"
include "nsyl4.mm"

theorem axc5c711to11
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x A. y ph -> A. y A. x ph )

  proof
    wph
    vy
    wal
    vx
    wal
    #
    @0
    wn
    #
    vy
    wal
    #
    wn
    #
    vy
    wal
    #
    wph
    vx
    wal
    #
    vy
    wal
    @4
    @0
    @1
    vy
    axc5c711toc7
    con4i
    @3
    @5
    vy
    @2
    vx
    wal
    #
    wn
    #
    vx
    wal
    @5
    @2
    @7
    wph
    vx
    @7
    @6
    @5
    wi
    wph
    @6
    @5
    pm2.21
    wph
    vx
    vy
    axc5c711
    syl
    alimi
    @2
    vx
    axc5c711toc7
    nsyl4
    alimi
    syl
end
