include "wa.mm"
include "simpl.mm"
include "imim1i.mm"

theorem pm3.41
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ch ) -> ( ( ph /\ ps ) -> ch ) )

  proof
    wph
    wps
    wa
    wph
    wch
    wph
    wps
    simpl
    imim1i
end
