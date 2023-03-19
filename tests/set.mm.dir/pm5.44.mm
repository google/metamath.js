include "wa.mm"
include "wi.mm"
include "jcab.mm"
include "baibr.mm"

theorem pm5.44
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ps ) -> ( ( ph -> ch ) <-> ( ph -> ( ps /\ ch ) ) ) )

  proof
    wph
    wps
    wch
    wa
    wi
    wph
    wps
    wi
    wph
    wch
    wi
    wph
    wps
    wch
    jcab
    baibr
end
