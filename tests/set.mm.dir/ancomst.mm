include "wa.mm"
include "ancom.mm"
include "imbi1i.mm"

theorem ancomst
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph /\ ps ) -> ch ) <-> ( ( ps /\ ph ) -> ch ) )

  proof
    wph
    wps
    wa
    wps
    wph
    wa
    wch
    wph
    wps
    ancom
    imbi1i
end
