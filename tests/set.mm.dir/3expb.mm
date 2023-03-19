include "3exp.mm"
include "imp32.mm"

theorem 3expb
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3exp.1: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ( ph /\ ( ps /\ ch ) ) -> th )

  proof
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    wth
    3exp.1
    3exp
    imp32
end
