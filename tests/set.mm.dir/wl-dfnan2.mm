include "wnan.mm"
include "wa.mm"
include "wn.mm"
include "wi.mm"
include "df-nan.mm"
include "imnan.mm"
include "bitr4i.mm"

theorem wl-dfnan2
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -/\ ps ) <-> ( ph -> -. ps ) )

  proof
    wph
    wps
    wnan
    wph
    wps
    wa
    wn
    wph
    wps
    wn
    wi
    wph
    wps
    df-nan
    wph
    wps
    imnan
    bitr4i
end
