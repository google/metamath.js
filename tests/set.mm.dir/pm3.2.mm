include "wa.mm"
include "id.mm"
include "ex.mm"

theorem pm3.2
  param wph: wff ph
  param wps: wff ps


  assert |- ( ph -> ( ps -> ( ph /\ ps ) ) )

  proof
    wph
    wps
    wph
    wps
    wa
    #
    @0
    id
    ex
end
