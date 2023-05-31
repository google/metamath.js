include "w3a.mm"
include "wa.mm"
include "df-3an.mm"
include "biimpri.mm"
include "exp31.mm"

theorem pm3.2an3
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch


  assert |- ( ph -> ( ps -> ( ch -> ( ph /\ ps /\ ch ) ) ) )

  proof
    wph
    wps
    wch
    wph
    wps
    wch
    w3a
    #
    @0
    wph
    wps
    wa
    wch
    wa
    wph
    wps
    wch
    df-3an
    biimpri
    exp31
end
