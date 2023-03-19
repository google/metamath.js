include "3coml.mm"

theorem 3comr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3exp.1: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ( ch /\ ph /\ ps ) -> th )

  proof
    wps
    wch
    wph
    wth
    wph
    wps
    wch
    wth
    3exp.1
    3coml
    3coml
end
