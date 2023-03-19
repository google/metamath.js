include "wa.mm"
include "wn.mm"
include "wo.mm"
include "w3a.mm"
include "tsan1.mm"
include "df-3an.mm"
include "orbi2i.mm"
include "sylibr.mm"

theorem ts3an1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( th -> ( ( -. ( ph /\ ps ) \/ -. ch ) \/ ( ph /\ ps /\ ch ) ) )

  proof
    wth
    wph
    wps
    wa
    #
    wn
    wch
    wn
    wo
    #
    @0
    wch
    wa
    #
    wo
    @1
    wph
    wps
    wch
    w3a
    #
    wo
    @0
    wch
    wth
    tsan1
    @3
    @2
    @1
    wph
    wps
    wch
    df-3an
    orbi2i
    sylibr
end
