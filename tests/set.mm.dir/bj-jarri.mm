include "wi.mm"
include "jarr.mm"
include "ax-mp.mm"

theorem bj-jarri
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume bj-jarri.1: |- ( ( ph -> ps ) -> ch )


  assert |- ( ps -> ch )

  proof
    wph
    wps
    wi
    wch
    wi
    wps
    wch
    wi
    bj-jarri.1
    wph
    wps
    wch
    jarr
    ax-mp
end
