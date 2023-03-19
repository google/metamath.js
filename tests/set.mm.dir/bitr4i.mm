include "bicomi.mm"
include "bitri.mm"

theorem bitr4i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume bitr4i.1: |- ( ph <-> ps )
  assume bitr4i.2: |- ( ch <-> ps )


  assert |- ( ph <-> ch )

  proof
    wph
    wps
    wch
    bitr4i.1
    wch
    wps
    bitr4i.2
    bicomi
    bitri
end
