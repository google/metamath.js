include "wnan.mm"
include "wa.mm"
include "wi.mm"
include "nannan.mm"
include "biimpi.mm"
include "simpr.mm"
include "imim2i.mm"
include "simpl.mm"
include "pm2.27.mm"
include "anim2d.mm"
include "expdimp.mm"
include "syl5com.mm"
include "ancr.mm"
include "anim1i.mm"
include "syl2anc.mm"
include "wn.mm"
include "con3.mm"
include "df-nan.mm"
include "3imtr4g.mm"
include "anim2i.mm"
include "biimpri.mm"
include "nanim.mm"
include "anim12i.mm"
include "4syl.mm"
include "mpbir.mm"

theorem lukshef-ax2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph -/\ ( ps -/\ ch ) ) -/\ ( ( ph -/\ ( ch -/\ ph ) ) -/\ ( ( th -/\ ps ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) ) )

  proof
    wph
    wps
    wch
    wnan
    wnan
    #
    wph
    wch
    wph
    wnan
    wnan
    #
    wth
    wps
    wnan
    #
    wph
    wth
    wnan
    #
    @3
    wnan
    wnan
    #
    wnan
    wnan
    @0
    @1
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
    wph
    wch
    wph
    wa
    wi
    #
    wph
    wth
    wa
    #
    wth
    wps
    wa
    #
    wi
    #
    wa
    #
    @8
    @2
    @3
    wi
    #
    wa
    @5
    @0
    @7
    wph
    wch
    wps
    nannan
    biimpi
    @7
    wph
    wch
    wi
    #
    @11
    @12
    @6
    wch
    wph
    wps
    wch
    simpr
    imim2i
    @7
    wph
    wps
    wi
    #
    @9
    @10
    @6
    wps
    wph
    wps
    wch
    simpl
    imim2i
    wph
    wth
    @15
    @10
    wph
    @15
    wps
    wth
    wph
    wps
    pm2.27
    anim2d
    expdimp
    syl5com
    @14
    @8
    @11
    wph
    wch
    ancr
    anim1i
    syl2anc
    @11
    @13
    @8
    @11
    @10
    wn
    @9
    wn
    @2
    @3
    @9
    @10
    con3
    wth
    wps
    df-nan
    wph
    wth
    df-nan
    3imtr4g
    anim2i
    @8
    @1
    @13
    @4
    @1
    @8
    wph
    wph
    wch
    nannan
    biimpri
    @13
    @4
    @2
    @3
    nanim
    biimpi
    anim12i
    4syl
    @0
    @4
    @1
    nannan
    mpbir
end
