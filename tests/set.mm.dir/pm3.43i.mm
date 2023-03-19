include "wa.mm"
include "pm3.2.mm"
include "imim3i.mm"

theorem pm3.43i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ps ) -> ( ( ph -> ch ) -> ( ph -> ( ps /\ ch ) ) ) )

  proof
    wps
    wch
    wps
    wch
    wa
    wph
    wps
    wch
    pm3.2
    imim3i
end
