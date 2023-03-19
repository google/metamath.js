include "wa.mm"
include "adantrr.mm"
include "adantll.mm"

theorem ad2ant2lr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume ad2ant2.1: |- ( ( ph /\ ps ) -> ch )


  assert |- ( ( ( th /\ ph ) /\ ( ps /\ ta ) ) -> ch )

  proof
    wph
    wps
    wta
    wa
    wch
    wth
    wph
    wps
    wch
    wta
    ad2ant2.1
    adantrr
    adantll
end
