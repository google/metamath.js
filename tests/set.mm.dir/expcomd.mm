include "expd.mm"
include "com23.mm"

theorem expcomd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume expcomd.1: |- ( ph -> ( ( ps /\ ch ) -> th ) )


  assert |- ( ph -> ( ch -> ( ps -> th ) ) )

  proof
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    wth
    expcomd.1
    expd
    com23
end
