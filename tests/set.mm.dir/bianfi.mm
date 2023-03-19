include "wa.mm"
include "intnan.mm"
include "2false.mm"

theorem bianfi
  let wph: wff ph
  let wps: wff ps
  assume bianfi.1: |- -. ph


  assert |- ( ph <-> ( ps /\ ph ) )

  proof
    wph
    wps
    wph
    wa
    bianfi.1
    wph
    wps
    bianfi.1
    intnan
    2false
end
