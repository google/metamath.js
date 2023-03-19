include "wi.mm"
include "wn.mm"
include "wo.mm"
include "wnan.mm"
include "con3.mm"
include "orim1d.mm"
include "wa.mm"
include "pm3.13.mm"
include "pm3.14.mm"
include "imim12i.mm"
include "df-nan.mm"
include "3imtr4g.mm"
include "syl.mm"

theorem naim1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ps ) -> ( ( ps -/\ ch ) -> ( ph -/\ ch ) ) )

  proof
    wph
    wps
    wi
    #
    wps
    wn
    #
    wch
    wn
    #
    wo
    #
    wph
    wn
    #
    @2
    wo
    #
    wi
    #
    wps
    wch
    wnan
    #
    wph
    wch
    wnan
    #
    wi
    @0
    @1
    @4
    @2
    wph
    wps
    con3
    orim1d
    @6
    wps
    wch
    wa
    wn
    #
    wph
    wch
    wa
    wn
    #
    @7
    @8
    @9
    @3
    @5
    @10
    wps
    wch
    pm3.13
    wph
    wch
    pm3.14
    imim12i
    wps
    wch
    df-nan
    wph
    wch
    df-nan
    3imtr4g
    syl
end
