include "wi.mm"
include "a1i.mm"
include "ax-mp.mm"

theorem bj-jarrii
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume bj-jarrii.1: |- ( ( ph -> ps ) -> ch )
  assume bj-jarrii.2: |- ps


  assert |- ch

  proof
    wph
    wps
    wi
    wch
    wps
    wph
    bj-jarrii.2
    a1i
    bj-jarrii.1
    ax-mp
end
