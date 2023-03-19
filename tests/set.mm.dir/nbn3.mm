include "wn.mm"
include "notnoti.mm"
include "nbn.mm"

theorem nbn3
  let wph: wff ph
  let wps: wff ps
  assume nbn3.1: |- ph


  assert |- ( -. ps <-> ( ps <-> -. ph ) )

  proof
    wph
    wn
    wps
    wph
    nbn3.1
    notnoti
    nbn
end
