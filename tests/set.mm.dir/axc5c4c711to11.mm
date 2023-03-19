include "wal.mm"
include "wi.mm"
include "ax-1.mm"
include "2alimi.mm"
include "wn.mm"
include "axc5c4c711toc7.mm"
include "con4i.mm"
include "pm2.21.mm"
include "axc5c4c711.mm"
include "sp.mm"
include "syl6.mm"
include "syl.mm"
include "alimi.mm"
include "nsyl4.mm"
include "pm2.27.mm"
include "id.mm"
include "mpg.mm"
include "3syl.mm"

theorem axc5c4c711to11
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x A. y ph -> A. y A. x ph )

  proof
    wph
    vy
    wal
    #
    vx
    wal
    wph
    wph
    wi
    #
    vy
    wal
    #
    wph
    wi
    #
    vy
    wal
    #
    vx
    wal
    #
    @3
    vx
    wal
    #
    vy
    wal
    #
    wph
    vx
    wal
    vy
    wal
    wph
    @3
    vx
    vy
    wph
    @2
    ax-1
    2alimi
    @5
    @5
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
    @7
    @11
    @5
    @8
    vy
    axc5c4c711toc7
    con4i
    @10
    @6
    vy
    @9
    vx
    wal
    #
    wn
    #
    vx
    wal
    @6
    @9
    @13
    @3
    vx
    @13
    @12
    @1
    @4
    wi
    #
    wi
    #
    @3
    @12
    @14
    pm2.21
    @15
    @2
    @0
    wph
    @1
    wph
    vx
    vy
    axc5c4c711
    wph
    vy
    sp
    syl6
    syl
    alimi
    @9
    vx
    axc5c4c711toc7
    nsyl4
    alimi
    syl
    @3
    wph
    vy
    vx
    @1
    @3
    wph
    wi
    vy
    @2
    wph
    pm2.27
    wph
    id
    mpg
    2alimi
    3syl
end
