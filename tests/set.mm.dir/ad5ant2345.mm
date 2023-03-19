include "wa.mm"
include "wi.mm"
include "exp41.mm"
include "adantl.mm"
include "imp41.mm"

theorem ad5ant2345
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ad5ant2345.1: |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta )


  assert |- ( ( ( ( ( et /\ ph ) /\ ps ) /\ ch ) /\ th ) -> ta )

  proof
    wet
    wph
    wa
    wps
    wch
    wth
    wta
    wph
    wps
    wch
    wth
    wta
    wi
    wi
    wi
    wet
    wph
    wps
    wch
    wth
    wta
    ad5ant2345.1
    exp41
    adantl
    imp41
end
