include "wal.mm"
include "wi.mm"
include "wn.mm"
include "axc4.mm"
include "hbn1.mm"
include "axc7.mm"
include "con1i.mm"
include "alrimih.mm"
include "ax-11.mm"
include "syl.mm"
include "nsyl4.mm"
include "pm2.21.mm"
include "spsd.mm"
include "ja.mm"

theorem axc5c4c711
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A. x A. y -. A. x A. y ( A. y ph -> ps ) -> ( ph -> A. y ( A. y ph -> ps ) ) ) -> ( A. y ph -> A. y ps ) )

  proof
    wph
    vy
    wal
    #
    wps
    wi
    #
    vy
    wal
    #
    vx
    wal
    wn
    #
    vy
    wal
    vx
    wal
    #
    wph
    @2
    wi
    @0
    wps
    vy
    wal
    #
    wi
    #
    @2
    @6
    @4
    wph
    wps
    vy
    axc4
    #
    @2
    wn
    #
    @3
    vx
    wal
    #
    vy
    wal
    @4
    @8
    @9
    vy
    @1
    vy
    hbn1
    @9
    @2
    @2
    vx
    axc7
    con1i
    alrimih
    @3
    vy
    vx
    ax-11
    syl
    nsyl4
    wph
    @2
    @6
    wph
    wn
    wph
    @5
    vy
    wph
    @5
    pm2.21
    spsd
    @7
    ja
    ja
end
