include "wn.mm"
include "wo.mm"
include "wb.mm"
include "notnot.mm"
include "biorf.mm"
include "syl.mm"

theorem biortn
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph -> ( ps <-> ( -. ph \/ ps ) ) )

  proof
    wph
    wph
    wn
    #
    wn
    wps
    @0
    wps
    wo
    wb
    wph
    notnot
    @0
    wps
    biorf
    syl
end
