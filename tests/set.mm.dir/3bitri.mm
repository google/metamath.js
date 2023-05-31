include "bitri.mm"

theorem 3bitri
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
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
