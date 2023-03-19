include "wi.mm"
include "mp2.mm"
include "ax-mp.mm"

theorem e000
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume e000.1: |- ph
  assume e000.2: |- ps
  assume e000.3: |- ch
  assume e000.4: |- ( ph -> ( ps -> ( ch -> th ) ) )


  assert |- th

  proof
    wch
    wth
    e000.3
    wph
    wps
    wch
    wth
    wi
    e000.1
    e000.2
    e000.4
    mp2
    ax-mp
end
