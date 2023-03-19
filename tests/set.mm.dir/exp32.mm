include "wa.mm"
include "ex.mm"
include "expd.mm"

theorem exp32
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume exp32.1: |- ( ( ph /\ ( ps /\ ch ) ) -> th )


  assert |- ( ph -> ( ps -> ( ch -> th ) ) )

  proof
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    wa
    wth
    exp32.1
    ex
    expd
end
