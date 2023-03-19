include "wa.mm"
include "ex.mm"
include "imdistani.mm"
include "sylan.mm"

theorem syldanl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume syldanl.1: |- ( ( ph /\ ps ) -> ch )
  assume syldanl.2: |- ( ( ( ph /\ ch ) /\ th ) -> ta )


  assert |- ( ( ( ph /\ ps ) /\ th ) -> ta )

  proof
    wph
    wps
    wa
    wph
    wch
    wa
    wth
    wta
    wph
    wps
    wch
    wph
    wps
    wch
    syldanl.1
    ex
    imdistani
    syldanl.2
    sylan
end
