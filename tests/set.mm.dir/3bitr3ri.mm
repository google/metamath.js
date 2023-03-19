include "bitr3i.mm"

theorem 3bitr3ri
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3bitr3i.1: |- ( ph <-> ps )
  assume 3bitr3i.2: |- ( ph <-> ch )
  assume 3bitr3i.3: |- ( ps <-> th )


  assert |- ( th <-> ch )

  proof
    wth
    wps
    wch
    3bitr3i.3
    wps
    wph
    wch
    3bitr3i.1
    3bitr3i.2
    bitr3i
    bitr3i
end
