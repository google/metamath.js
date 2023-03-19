include "wi.mm"
include "wn.mm"
include "wo.mm"
include "wnan.mm"
include "con3.mm"
include "orim2d.mm"
include "wa.mm"
include "pm3.13.mm"
include "pm3.14.mm"
include "imim12i.mm"
include "df-nan.mm"
include "3imtr4g.mm"
include "syl.mm"

theorem naim2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ps ) -> ( ( ch -/\ ps ) -> ( ch -/\ ph ) ) )

  proof
    wph
    wps
    wi
    #
    wch
    wn
    #
    wps
    wn
    #
    wo
    #
    @1
    wph
    wn
    #
    wo
    #
    wi
    #
    wch
    wps
    wnan
    #
    wch
    wph
    wnan
    #
    wi
    @0
    @2
    @4
    @1
    wph
    wps
    con3
    orim2d
    @6
    wch
    wps
    wa
    wn
    #
    wch
    wph
    wa
    wn
    #
    @7
    @8
    @9
    @3
    @5
    @10
    wch
    wps
    pm3.13
    wch
    wph
    pm3.14
    imim12i
    wch
    wps
    df-nan
    wch
    wph
    df-nan
    3imtr4g
    syl
end
