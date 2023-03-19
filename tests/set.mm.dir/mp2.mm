include "wi.mm"
include "ax-mp.mm"

theorem mp2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume mp2.1: |- ph
  assume mp2.2: |- ps
  assume mp2.3: |- ( ph -> ( ps -> ch ) )


  assert |- ch

  proof
    wps
    wch
    mp2.2
    wph
    wps
    wch
    wi
    mp2.1
    mp2.3
    ax-mp
    ax-mp
end
