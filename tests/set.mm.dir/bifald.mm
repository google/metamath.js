include "wn.mm"
include "wfal.mm"
include "wb.mm"
include "id.mm"
include "falim.mm"
include "pm5.21ni.mm"
include "syl.mm"

theorem bifald
  let wph: wff ph
  let wps: wff ps
  assume bifald.1: |- ( ph -> -. ps )


  assert |- ( ph -> ( ps <-> F. ) )

  proof
    wph
    wps
    wn
    wps
    wfal
    wb
    bifald.1
    wps
    wps
    wfal
    wps
    id
    wps
    falim
    pm5.21ni
    syl
end
