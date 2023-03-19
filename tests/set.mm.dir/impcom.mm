include "com12.mm"
include "imp.mm"

theorem impcom
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume imp.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( ( ps /\ ph ) -> ch )

  proof
    wps
    wph
    wch
    wph
    wps
    wch
    imp.1
    com12
    imp
end
