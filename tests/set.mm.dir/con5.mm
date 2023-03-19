include "wn.mm"
include "wb.mm"
include "biimpr.mm"
include "con1d.mm"

theorem con5
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph <-> -. ps ) -> ( -. ph -> ps ) )

  proof
    wph
    wps
    wn
    #
    wb
    wps
    wph
    wph
    @0
    biimpr
    con1d
end
