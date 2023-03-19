include "wa.mm"
include "wb.mm"
include "ibar.mm"
include "ax-mp.mm"

theorem biantrur
  let wph: wff ph
  let wps: wff ps
  assume biantrur.1: |- ph


  assert |- ( ps <-> ( ph /\ ps ) )

  proof
    wph
    wps
    wph
    wps
    wa
    wb
    biantrur.1
    wph
    wps
    ibar
    ax-mp
end
