include "wa.mm"
include "anc2li.mm"
include "imp.mm"

theorem imdistani
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume imdistani.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( ( ph /\ ps ) -> ( ph /\ ch ) )

  proof
    wph
    wps
    wph
    wch
    wa
    wph
    wps
    wch
    imdistani.1
    anc2li
    imp
end
