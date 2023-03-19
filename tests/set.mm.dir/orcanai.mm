include "wn.mm"
include "ord.mm"
include "imp.mm"

theorem orcanai
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume orcanai.1: |- ( ph -> ( ps \/ ch ) )


  assert |- ( ( ph /\ -. ps ) -> ch )

  proof
    wph
    wps
    wn
    wch
    wph
    wps
    wch
    orcanai.1
    ord
    imp
end
