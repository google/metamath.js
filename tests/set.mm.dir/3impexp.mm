include "w3a.mm"
include "wi.mm"
include "id.mm"
include "3expd.mm"
include "3impd.mm"
include "impbii.mm"

theorem 3impexp
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph /\ ps /\ ch ) -> th ) <-> ( ph -> ( ps -> ( ch -> th ) ) ) )

  proof
    wph
    wps
    wch
    w3a
    wth
    wi
    #
    wph
    wps
    wch
    wth
    wi
    wi
    wi
    #
    @0
    wph
    wps
    wch
    wth
    @0
    id
    3expd
    @1
    wph
    wps
    wch
    wth
    @1
    id
    3impd
    impbii
end
