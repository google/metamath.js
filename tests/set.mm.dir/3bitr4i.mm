include "bitr4i.mm"
include "bitri.mm"

theorem 3bitr4i
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume 3bitr4i.1: |- ( ph <-> ps )
  assume 3bitr4i.2: |- ( ch <-> ph )
  assume 3bitr4i.3: |- ( th <-> ps )


  assert |- ( ch <-> th )

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
    bitri
end
