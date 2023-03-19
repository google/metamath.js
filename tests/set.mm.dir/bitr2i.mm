include "bitri.mm"
include "bicomi.mm"

theorem bitr2i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume bitr2i.1: |- ( ph <-> ps )
  assume bitr2i.2: |- ( ps <-> ch )


  assert |- ( ch <-> ph )

  proof
    wph
    wch
    wph
    wps
    wch
    bitr2i.1
    bitr2i.2
    bitri
    bicomi
end
