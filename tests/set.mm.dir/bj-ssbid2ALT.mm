include "wssb.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "df-ssb.mm"
include "sp.mm"
include "imim2i.mm"
include "alimi.mm"
include "wex.mm"
include "pm2.21.mm"
include "equcomi.mm"
include "imim1i.mm"
include "ja.mm"
include "ax6ev.mm"
include "19.23v.mm"
include "biimpi.mm"
include "mpisyl.mm"
include "syl.mm"
include "sylbi.mm"

theorem bj-ssbid2ALT
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( [b x /b x ]b ph -> ph )

  proof
    wph
    vx
    vx
    wssb
    vy
    vx
    weq
    #
    vx
    vy
    weq
    #
    wph
    wi
    #
    vx
    wal
    #
    wi
    #
    vy
    wal
    #
    wph
    wph
    vx
    vy
    vx
    df-ssb
    @5
    @0
    @2
    wi
    #
    vy
    wal
    #
    wph
    @4
    @6
    vy
    @3
    @2
    @0
    @2
    vx
    sp
    imim2i
    alimi
    @7
    @0
    wph
    wi
    #
    vy
    wal
    #
    @0
    vy
    wex
    #
    wph
    @6
    @8
    vy
    @0
    @2
    @8
    @0
    wph
    pm2.21
    @0
    @1
    wph
    vy
    vx
    equcomi
    imim1i
    ja
    alimi
    vy
    vx
    ax6ev
    @9
    @10
    wph
    wi
    @0
    wph
    vy
    19.23v
    biimpi
    mpisyl
    syl
    sylbi
end
