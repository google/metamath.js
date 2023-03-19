include "bitr3i.mm"
include "bitri.mm"

theorem 3bitr3i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
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
