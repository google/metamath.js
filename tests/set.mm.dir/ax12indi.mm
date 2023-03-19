include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "ax12indn.mm"
include "imp.mm"
include "pm2.21.mm"
include "imim2i.mm"
include "alimi.mm"
include "syl6.mm"
include "ax-1.mm"
include "jad.mm"
include "ex.mm"

theorem ax12indi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume ax12indn.1: |- ( -. A. x x = y -> ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) )
  assume ax12indi.2: |- ( -. A. x x = y -> ( x = y -> ( ps -> A. x ( x = y -> ps ) ) ) )


  assert |- ( -. A. x x = y -> ( x = y -> ( ( ph -> ps ) -> A. x ( x = y -> ( ph -> ps ) ) ) ) )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    wn
    #
    @0
    wph
    wps
    wi
    #
    @0
    @2
    wi
    #
    vx
    wal
    #
    wi
    @1
    @0
    wa
    #
    wph
    wps
    @4
    @5
    wph
    wn
    #
    @0
    @6
    wi
    #
    vx
    wal
    #
    @4
    @1
    @0
    @6
    @8
    wi
    wph
    vx
    vy
    ax12indn.1
    ax12indn
    imp
    @7
    @3
    vx
    @6
    @2
    @0
    wph
    wps
    pm2.21
    imim2i
    alimi
    syl6
    @5
    wps
    @0
    wps
    wi
    #
    vx
    wal
    #
    @4
    @1
    @0
    wps
    @10
    wi
    ax12indi.2
    imp
    @9
    @3
    vx
    wps
    @2
    @0
    wps
    wph
    ax-1
    imim2i
    alimi
    syl6
    jad
    ex
end
