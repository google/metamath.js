include "wa.mm"
include "wn.mm"
include "wo.mm"
include "w3a.mm"
include "tsan2.mm"
include "df-3an.mm"
include "notbii.mm"
include "orbi2i.mm"
include "sylibr.mm"

theorem ts3an2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( th -> ( ( ph /\ ps ) \/ -. ( ph /\ ps /\ ch ) ) )

  proof
    wth
    wph
    wps
    wa
    #
    @0
    wch
    wa
    #
    wn
    #
    wo
    @0
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
    tsan2
    @4
    @2
    @0
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
