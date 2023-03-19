include "wal.mm"
include "wi.mm"
include "wa.mm"
include "hba1.mm"
include "hban.mm"
include "wn.mm"
include "hbntal.mm"
include "adantr.mm"
include "19.21bi.mm"
include "pm2.21.mm"
include "alimi.mm"
include "syl6.mm"
include "simpr.mm"
include "ax-1.mm"
include "jad.mm"
include "alrimih.mm"

theorem hbimpg
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( ( A. x ( ph -> A. x ph ) /\ A. x ( ps -> A. x ps ) ) -> A. x ( ( ph -> ps ) -> A. x ( ph -> ps ) ) )

  proof
    wph
    wph
    vx
    wal
    wi
    #
    vx
    wal
    #
    wps
    wps
    vx
    wal
    #
    wi
    #
    vx
    wal
    #
    wa
    #
    wph
    wps
    wi
    #
    @6
    vx
    wal
    #
    wi
    vx
    @1
    @4
    vx
    @0
    vx
    hba1
    @3
    vx
    hba1
    hban
    @5
    wph
    wps
    @7
    @5
    wph
    wn
    #
    @8
    vx
    wal
    #
    @7
    @5
    @8
    @9
    wi
    #
    vx
    @1
    @10
    vx
    wal
    @4
    wph
    vx
    hbntal
    adantr
    19.21bi
    @8
    @6
    vx
    wph
    wps
    pm2.21
    alimi
    syl6
    @5
    wps
    @2
    @7
    @5
    @3
    vx
    @1
    @4
    simpr
    19.21bi
    wps
    @6
    vx
    wps
    wph
    ax-1
    alimi
    syl6
    jad
    alrimih
end
