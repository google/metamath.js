include "wmo.mm"
include "wa.mm"
include "moan.mm"
include "ax-mp.mm"

theorem moani
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume moani.1: |- E* x ph


  assert |- E* x ( ps /\ ph )

  proof
    wph
    vx
    wmo
    wps
    wph
    wa
    vx
    wmo
    moani.1
    wph
    wps
    vx
    moan
    ax-mp
end
