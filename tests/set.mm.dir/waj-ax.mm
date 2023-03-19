include "wnan.mm"
include "wa.mm"
include "wi.mm"
include "nannan.mm"
include "wn.mm"
include "simpr.mm"
include "imim2i.mm"
include "pm2.27.mm"
include "anim2d.mm"
include "expdimp.mm"
include "syl5com.mm"
include "con3d.mm"
include "df-nan.mm"
include "3imtr4g.mm"
include "nanim.mm"
include "sylib.mm"
include "pm3.21.mm"
include "adantr.mm"
include "com12.mm"
include "a2i.mm"
include "sylibr.mm"
include "jca.mm"
include "sylbi.mm"
include "mpbir.mm"

theorem waj-ax
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph -/\ ( ps -/\ ch ) ) -/\ ( ( ( th -/\ ch ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) -/\ ( ph -/\ ( ph -/\ ps ) ) ) )

  proof
    wph
    wps
    wch
    wnan
    wnan
    #
    wth
    wch
    wnan
    #
    wph
    wth
    wnan
    #
    @2
    wnan
    wnan
    #
    wph
    wph
    wps
    wnan
    wnan
    #
    wnan
    wnan
    @0
    @3
    @4
    wa
    #
    wi
    @0
    wph
    wps
    wch
    wa
    #
    wi
    #
    @5
    wph
    wch
    wps
    nannan
    @7
    @3
    @4
    @7
    @1
    @2
    wi
    @3
    @7
    wth
    wch
    wa
    #
    wn
    wph
    wth
    wa
    #
    wn
    @1
    @2
    @7
    @9
    @8
    @7
    wph
    wch
    wi
    #
    @9
    @8
    @6
    wch
    wph
    wps
    wch
    simpr
    imim2i
    wph
    wth
    @10
    @8
    wph
    @10
    wch
    wth
    wph
    wch
    pm2.27
    anim2d
    expdimp
    syl5com
    con3d
    wth
    wch
    df-nan
    wph
    wth
    df-nan
    3imtr4g
    @1
    @2
    nanim
    sylib
    @7
    wph
    wph
    wps
    wa
    #
    wi
    #
    @4
    wph
    @6
    @11
    @6
    wph
    @11
    wps
    @12
    wch
    wps
    wph
    pm3.21
    adantr
    com12
    a2i
    wph
    wps
    wph
    nannan
    sylibr
    jca
    sylbi
    @0
    @4
    @3
    nannan
    mpbir
end
