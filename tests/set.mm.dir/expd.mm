include "wi.mm"
include "wa.mm"
include "com12.mm"
include "ex.mm"
include "com3r.mm"

theorem expd
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume expd.1: |- ( ph -> ( ( ps /\ ch ) -> th ) )


  assert |- ( ph -> ( ps -> ( ch -> th ) ) )

  proof
    wps
    wch
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
    wa
    wth
    expd.1
    com12
    ex
    com3r
end
