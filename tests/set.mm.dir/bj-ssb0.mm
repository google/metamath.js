include "wssb.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "df-ssb.mm"
include "wex.mm"
include "19.23v.mm"
include "ax6ev.mm"
include "pm2.27.mm"
include "ax-mp.mm"
include "ax-1.mm"
include "impbii.mm"
include "bitri.mm"
include "imbi2i.mm"
include "albii.mm"

theorem bj-ssb0
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let vy: setvar y

  disjoint ph x
  disjoint x y
  disjoint ph y
  disjoint t y
  assert |- ( [b t /b x ]b ph <-> ph )

  proof
    wph
    vx
    vt
    wssb
    vy
    vt
    weq
    #
    vx
    vy
    weq
    #
    wph
    wi
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
    vt
    df-ssb
    @4
    @0
    vy
    wex
    #
    wph
    wi
    #
    wph
    @4
    @0
    wph
    wi
    #
    vy
    wal
    @6
    @3
    @7
    vy
    @2
    wph
    @0
    @2
    @1
    vx
    wex
    #
    wph
    wi
    #
    wph
    @1
    wph
    vx
    19.23v
    @9
    wph
    @8
    @9
    wph
    wi
    vx
    vy
    ax6ev
    @8
    wph
    pm2.27
    ax-mp
    wph
    @8
    ax-1
    impbii
    bitri
    imbi2i
    albii
    @0
    wph
    vy
    19.23v
    bitri
    @6
    wph
    @5
    @6
    wph
    wi
    vy
    vt
    ax6ev
    @5
    wph
    pm2.27
    ax-mp
    wph
    @5
    ax-1
    impbii
    bitri
    bitri
end
