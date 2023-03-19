include "wb.mm"
include "bibi1.mm"
include "biimpd.mm"

theorem bitr3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph <-> ps ) -> ( ( ph <-> ch ) -> ( ps <-> ch ) ) )

  proof
    wph
    wps
    wb
    wph
    wch
    wb
    wps
    wch
    wb
    wph
    wps
    wch
    bibi1
    biimpd
end
