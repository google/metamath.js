include "wal.mm"
include "wn.mm"
include "wi.mm"
include "ax-1.mm"
include "alimi.mm"
include "axc4i.mm"
include "con3i.mm"
include "sps.mm"
include "pm2.21.mm"
include "axc5c4c711.mm"
include "syl.mm"
include "sp.mm"
include "syl6.mm"
include "pm2.27.mm"
include "id.mm"
include "mpg.mm"
include "3syl.mm"

theorem axc5c4c711toc7
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
    wph
    wph
    wi
    #
    vx
    wal
    #
    wph
    wi
    #
    vx
    wal
    #
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
    #
    @5
    wph
    @10
    @2
    @9
    @2
    vx
    @8
    @1
    vx
    @0
    @7
    wph
    @6
    vx
    wph
    @5
    vx
    wph
    @4
    ax-1
    alimi
    axc4i
    con3i
    alimi
    sps
    con3i
    @11
    @4
    @0
    wph
    @11
    @10
    @3
    @6
    wi
    #
    wi
    @4
    @0
    wi
    @10
    @12
    pm2.21
    @3
    wph
    vx
    vx
    axc5c4c711
    syl
    wph
    vx
    sp
    syl6
    @3
    @5
    wph
    wi
    vx
    @4
    wph
    pm2.27
    wph
    id
    mpg
    3syl
end
