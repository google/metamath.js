include "wa.mm"
include "wi.mm"
include "com3l.mm"
include "imp.mm"
include "com12.mm"

theorem impd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume impd.1: |- ( ph -> ( ps -> ( ch -> th ) ) )


  assert |- ( ph -> ( ( ps /\ ch ) -> th ) )

  proof
    wps
    wch
    wa
    wph
    wth
    wps
    wch
    wph
    wth
    wi
    wph
    wps
    wch
    wth
    impd.1
    com3l
    imp
    com12
end
