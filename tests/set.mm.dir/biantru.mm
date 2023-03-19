include "wa.mm"
include "wb.mm"
include "iba.mm"
include "ax-mp.mm"

theorem biantru
  let wph: wff ph
  let wps: wff ps
  assume biantru.1: |- ph


  assert |- ( ps <-> ( ps /\ ph ) )

  proof
    wph
    wps
    wps
    wph
    wa
    wb
    biantru.1
    wph
    wps
    iba
    ax-mp
end
