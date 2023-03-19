include "wa.mm"
include "wi.mm"
include "impexp.mm"
include "imbi2i.mm"

theorem impexpd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph -> ( ( ps /\ ch ) -> th ) ) <-> ( ph -> ( ps -> ( ch -> th ) ) ) )

  proof
    wps
    wch
    wa
    wth
    wi
    wps
    wch
    wth
    wi
    wi
    wph
    wps
    wch
    wth
    impexp
    imbi2i
end
