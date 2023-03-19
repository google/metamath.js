include "wn.mm"
include "a1i.mm"
include "orri.mm"

theorem olci
  let wph: wff ph
  let wps: wff ps
  assume orci.1: |- ph


  assert |- ( ps \/ ph )

  proof
    wps
    wph
    wph
    wps
    wn
    orci.1
    a1i
    orri
end
