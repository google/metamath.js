include "sylancl.mm"

theorem ee10an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume ee10an.1: |- ( ph -> ps )
  assume ee10an.2: |- ch
  assume ee10an.3: |- ( ( ps /\ ch ) -> th )


  assert |- ( ph -> th )

  proof
    wph
    wps
    wch
    wth
    ee10an.1
    ee10an.2
    ee10an.3
    sylancl
end
