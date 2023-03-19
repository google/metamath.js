include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wnan.mm"
include "tsan2.mm"
include "df-nan.mm"
include "orbi2i.mm"
include "sylibr.mm"

theorem tsna2
  let wph: wff ph
  let wps: wff ps
  let wth: wff th


  assert |- ( th -> ( ph \/ ( ph -/\ ps ) ) )

  proof
    wth
    wph
    wph
    wps
    wa
    wn
    #
    wo
    wph
    wph
    wps
    wnan
    #
    wo
    wph
    wps
    wth
    tsan2
    @1
    @0
    wph
    wph
    wps
    df-nan
    orbi2i
    sylibr
end
