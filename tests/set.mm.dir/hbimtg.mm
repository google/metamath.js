include "wal.mm"
include "wi.mm"
include "wa.mm"
include "wn.mm"
include "hbntg.mm"
include "pm2.21.mm"
include "alimi.mm"
include "syl6.mm"
include "adantr.mm"
include "ala1.mm"
include "imim2i.mm"
include "adantl.mm"
include "jad.mm"

theorem hbimtg
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x


  assert |- ( ( A. x ( ph -> A. x ch ) /\ ( ps -> A. x th ) ) -> ( ( ch -> ps ) -> A. x ( ph -> th ) ) )

  proof
    wph
    wch
    vx
    wal
    wi
    vx
    wal
    #
    wps
    wth
    vx
    wal
    #
    wi
    #
    wa
    wch
    wps
    wph
    wth
    wi
    #
    vx
    wal
    #
    @0
    wch
    wn
    #
    @4
    wi
    @2
    @0
    @5
    wph
    wn
    #
    vx
    wal
    @4
    wph
    wch
    vx
    hbntg
    @6
    @3
    vx
    wph
    wth
    pm2.21
    alimi
    syl6
    adantr
    @2
    wps
    @4
    wi
    @0
    @1
    @4
    wps
    wth
    wph
    vx
    ala1
    imim2i
    adantl
    jad
end
