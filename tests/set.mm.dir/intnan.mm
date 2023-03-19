include "wa.mm"
include "simpr.mm"
include "mto.mm"

theorem intnan
  let wph: wff ph
  let wps: wff ps
  assume intnan.1: |- -. ph


  assert |- -. ( ps /\ ph )

  proof
    wps
    wph
    wa
    wph
    intnan.1
    wps
    wph
    simpr
    mto
end
