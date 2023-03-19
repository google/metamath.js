include "wnan.mm"
include "wa.mm"
include "wn.mm"
include "df-nan.mm"
include "ancom.mm"
include "xchbinx.mm"
include "bitr4i.mm"

theorem nancom
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -/\ ps ) <-> ( ps -/\ ph ) )

  proof
    wph
    wps
    wnan
    #
    wps
    wph
    wa
    #
    wn
    wps
    wph
    wnan
    @0
    wph
    wps
    wa
    @1
    wph
    wps
    df-nan
    wph
    wps
    ancom
    xchbinx
    wps
    wph
    df-nan
    bitr4i
end
