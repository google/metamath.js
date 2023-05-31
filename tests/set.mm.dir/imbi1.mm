include "wb.mm"
include "id.mm"
include "imbi1d.mm"

theorem imbi1
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch


  assert |- ( ( ph <-> ps ) -> ( ( ph -> ch ) <-> ( ps -> ch ) ) )

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
    imbi1d
end
