include "wb.mm"
include "id.mm"
include "bibi1d.mm"

theorem bibi1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph <-> ps ) -> ( ( ph <-> ch ) <-> ( ps <-> ch ) ) )

  proof
    wph
    wps
    wb
    #
    wph
    wps
    wch
    @0
    id
    bibi1d
end
