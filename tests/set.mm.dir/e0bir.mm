include "mpbir.mm"

theorem e0bir
  let wph: wff ph
  let wps: wff ps
  assume e0bir.1: |- ph
  assume e0bir.2: |- ( ps <-> ph )


  assert |- ps

  proof
    wps
    wph
    e0bir.1
    e0bir.2
    mpbir
end
