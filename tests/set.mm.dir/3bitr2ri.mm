include "bitr4i.mm"
include "bitr2i.mm"

theorem 3bitr2ri
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3bitr2i.1: |- ( ph <-> ps )
  assume 3bitr2i.2: |- ( ch <-> ps )
  assume 3bitr2i.3: |- ( ch <-> th )


  assert |- ( th <-> ph )

  proof
    wph
    wch
    wth
    wph
    wps
    wch
    3bitr2i.1
    3bitr2i.2
    bitr4i
    3bitr2i.3
    bitr2i
end
