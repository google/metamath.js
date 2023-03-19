include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wnan.mm"
include "tsan3.mm"
include "df-nan.mm"
include "orbi2i.mm"
include "sylibr.mm"

theorem tsna3
  let wph: wff ph
  let wps: wff ps
  let wth: wff th


  assert |- ( th -> ( ps \/ ( ph -/\ ps ) ) )

  proof
    wth
    wps
    wph
    wps
    wa
    wn
    #
    wo
    wps
    wph
    wps
    wnan
    #
    wo
    wph
    wps
    wth
    tsan3
    @1
    @0
    wps
    wph
    wps
    df-nan
    orbi2i
    sylibr
end
