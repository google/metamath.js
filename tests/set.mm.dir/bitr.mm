include "wb.mm"
include "bibi1.mm"
include "biimpar.mm"

theorem bitr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph <-> ps ) /\ ( ps <-> ch ) ) -> ( ph <-> ch ) )

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
    biimpar
end
