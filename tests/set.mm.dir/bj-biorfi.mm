include "wn.mm"
include "wo.mm"
include "wb.mm"
include "biorf.mm"
include "ax-mp.mm"

theorem bj-biorfi
  let wph: wff ph
  let wps: wff ps
  assume bj-biorfi.1: |- -. ph


  assert |- ( ps <-> ( ph \/ ps ) )

  proof
    wph
    wn
    wps
    wph
    wps
    wo
    wb
    bj-biorfi.1
    wph
    wps
    biorf
    ax-mp
end
