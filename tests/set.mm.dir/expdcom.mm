include "expd.mm"
include "com3l.mm"

theorem expdcom
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume expdcom.1: |- ( ph -> ( ( ps /\ ch ) -> th ) )


  assert |- ( ps -> ( ch -> ( ph -> th ) ) )

  proof
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    wth
    expdcom.1
    expd
    com3l
end
