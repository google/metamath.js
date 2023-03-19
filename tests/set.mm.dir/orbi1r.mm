include "wb.mm"
include "id.mm"
include "orbi2d.mm"

theorem orbi1r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph <-> ps ) -> ( ( ch \/ ph ) <-> ( ch \/ ps ) ) )

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
    orbi2d
end
