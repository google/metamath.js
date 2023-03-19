include "wn.mm"
include "wo.mm"
include "wa.mm"
include "wnan.mm"
include "tsan1.mm"
include "notnotb.mm"
include "df-nan.mm"
include "bitr3i.mm"
include "con4bii.mm"
include "orbi2i.mm"
include "sylibr.mm"

theorem tsna1
  let wph: wff ph
  let wps: wff ps
  let wth: wff th


  assert |- ( th -> ( ( -. ph \/ -. ps ) \/ -. ( ph -/\ ps ) ) )

  proof
    wth
    wph
    wn
    wps
    wn
    wo
    #
    wph
    wps
    wa
    #
    wo
    @0
    wph
    wps
    wnan
    #
    wn
    #
    wo
    wph
    wps
    wth
    tsan1
    @3
    @1
    @0
    @3
    @1
    @3
    wn
    @2
    @1
    wn
    @2
    notnotb
    wph
    wps
    df-nan
    bitr3i
    con4bii
    orbi2i
    sylibr
end
