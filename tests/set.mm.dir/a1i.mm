include "wi.mm"
include "ax-1.mm"
include "ax-mp.mm"

theorem a1i
  let wph: wff ph
  let wps: wff ps
  assume a1i.1: |- ph


  assert |- ( ps -> ph )

  proof
    wph
    wps
    wph
    wi
    a1i.1
    wph
    wps
    ax-1
    ax-mp
end
