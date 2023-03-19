include "bitri.mm"

theorem 3bitri
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3bitri.1: |- ( ph <-> ps )
  assume 3bitri.2: |- ( ps <-> ch )
  assume 3bitri.3: |- ( ch <-> th )


  assert |- ( ph <-> th )

  proof
    wph
    wps
    wth
    3bitri.1
    wps
    wch
    wth
    3bitri.2
    3bitri.3
    bitri
    bitri
end
