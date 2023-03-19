include "3com23.mm"
include "3com13.mm"

theorem 3coml
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3exp.1: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ( ps /\ ch /\ ph ) -> th )

  proof
    wph
    wch
    wps
    wth
    wph
    wps
    wch
    wth
    3exp.1
    3com23
    3com13
end
