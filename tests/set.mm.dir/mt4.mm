include "con4i.mm"
include "ax-mp.mm"

theorem mt4
  let wph: wff ph
  let wps: wff ps
  assume mt4.1: |- ph
  assume mt4.2: |- ( -. ps -> -. ph )


  assert |- ps

  proof
    wph
    wps
    mt4.1
    wps
    wph
    mt4.2
    con4i
    ax-mp
end
