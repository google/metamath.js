include "wn.mm"
include "wi.mm"
include "wnan.mm"
include "con2b.mm"
include "wl-dfnan2.mm"
include "3bitr4i.mm"

theorem wl-nancom
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -/\ ps ) <-> ( ps -/\ ph ) )

  proof
    wph
    wps
    wn
    wi
    wps
    wph
    wn
    wi
    wph
    wps
    wnan
    wps
    wph
    wnan
    wph
    wps
    con2b
    wph
    wps
    wl-dfnan2
    wps
    wph
    wl-dfnan2
    3bitr4i
end
