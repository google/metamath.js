include "wa.mm"
include "wi.mm"
include "com3l.mm"
include "imp.mm"
include "com12.mm"

theorem impd
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
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
