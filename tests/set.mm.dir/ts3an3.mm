include "wa.mm"
include "wn.mm"
include "wo.mm"
include "w3a.mm"
include "tsan3.mm"
include "df-3an.mm"
include "notbii.mm"
include "orbi2i.mm"
include "sylibr.mm"

theorem ts3an3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( th -> ( ch \/ -. ( ph /\ ps /\ ch ) ) )

  proof
    wth
    wch
    wph
    wps
    wa
    #
    wch
    wa
    #
    wn
    #
    wo
    wch
    wph
    wps
    wch
    w3a
    #
    wn
    #
    wo
    @0
    wch
    wth
    tsan3
    @4
    @2
    wch
    @3
    @1
    wph
    wps
    wch
    df-3an
    notbii
    orbi2i
    sylibr
end
