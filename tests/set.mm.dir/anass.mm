include "wa.mm"
include "id.mm"
include "anassrs.mm"
include "anasss.mm"
include "impbii.mm"

theorem anass
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch


  assert |- ( ( ( ph /\ ps ) /\ ch ) <-> ( ph /\ ( ps /\ ch ) ) )

  proof
    wph
    wps
    wa
    wch
    wa
    #
    wph
    wps
    wch
    wa
    wa
    #
    wph
    wps
    wch
    @1
    @1
    id
    anassrs
    wph
    wps
    wch
    @0
    @0
    id
    anasss
    impbii
end
