include "wa.mm"
include "anidm.mm"
include "imbi2i.mm"

theorem anidmdbi
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ( ps /\ ps ) ) <-> ( ph -> ps ) )

  proof
    wps
    wps
    wa
    wps
    wph
    wps
    anidm
    imbi2i
end
