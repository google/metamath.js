include "w3a.mm"
include "pm3.2an3.mm"
include "syl8.mm"

theorem 3exp
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3exp.1: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ph -> ( ps -> ( ch -> th ) ) )

  proof
    wph
    wps
    wch
    wph
    wps
    wch
    w3a
    wth
    wph
    wps
    wch
    pm3.2an3
    3exp.1
    syl8
end
