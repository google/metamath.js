include "bitr3i.mm"
include "bitri.mm"

theorem 3bitr3i
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume 3bitr3i.1: |- ( ph <-> ps )
  assume 3bitr3i.2: |- ( ph <-> ch )
  assume 3bitr3i.3: |- ( ps <-> th )


  assert |- ( ch <-> th )

  proof
    wch
    wps
    wth
    wch
    wph
    wps
    3bitr3i.2
    3bitr3i.1
    bitr3i
    3bitr3i.3
    bitri
end
