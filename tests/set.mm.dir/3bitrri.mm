include "bitr2i.mm"
include "bitr3i.mm"

theorem 3bitrri
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3bitri.1: |- ( ph <-> ps )
  assume 3bitri.2: |- ( ps <-> ch )
  assume 3bitri.3: |- ( ch <-> th )


  assert |- ( th <-> ph )

  proof
    wth
    wch
    wph
    3bitri.3
    wph
    wps
    wch
    3bitri.1
    3bitri.2
    bitr2i
    bitr3i
end
