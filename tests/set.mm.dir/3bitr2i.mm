include "bitr4i.mm"
include "bitri.mm"

theorem 3bitr2i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3bitr2i.1: |- ( ph <-> ps )
  assume 3bitr2i.2: |- ( ch <-> ps )
  assume 3bitr2i.3: |- ( ch <-> th )


  assert |- ( ph <-> th )

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
    bitri
end
