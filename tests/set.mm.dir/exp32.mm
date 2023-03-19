include "wa.mm"
include "ex.mm"
include "expd.mm"

theorem exp32
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
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
