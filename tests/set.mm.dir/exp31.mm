include "wi.mm"
include "wa.mm"
include "ex.mm"

theorem exp31
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume exp31.1: |- ( ( ( ph /\ ps ) /\ ch ) -> th )


  assert |- ( ph -> ( ps -> ( ch -> th ) ) )

  proof
    wph
    wps
    wch
    wth
    wi
    wph
    wps
    wa
    wch
    wth
    exp31.1
    ex
    ex
end
