include "wi.mm"
include "wo.mm"
include "pm3.48.mm"
include "syl2anc.mm"

theorem orim12d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume orim12d.1: |- ( ph -> ( ps -> ch ) )
  assume orim12d.2: |- ( ph -> ( th -> ta ) )


  assert |- ( ph -> ( ( ps \/ th ) -> ( ch \/ ta ) ) )

  proof
    wph
    wps
    wch
    wi
    wth
    wta
    wi
    wps
    wth
    wo
    wch
    wta
    wo
    wi
    orim12d.1
    orim12d.2
    wps
    wch
    wth
    wta
    pm3.48
    syl2anc
end
