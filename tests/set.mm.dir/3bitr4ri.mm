include "bitr4i.mm"
include "bitr2i.mm"

theorem 3bitr4ri
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3bitr4i.1: |- ( ph <-> ps )
  assume 3bitr4i.2: |- ( ch <-> ph )
  assume 3bitr4i.3: |- ( th <-> ps )


  assert |- ( th <-> ch )

  proof
    wch
    wph
    wth
    3bitr4i.2
    wph
    wps
    wth
    3bitr4i.1
    3bitr4i.3
    bitr4i
    bitr2i
end
