include "wb.mm"
include "id.mm"
include "imbi2d.mm"

theorem imbi2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph <-> ps ) -> ( ( ch -> ph ) <-> ( ch -> ps ) ) )

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
    imbi2d
end
