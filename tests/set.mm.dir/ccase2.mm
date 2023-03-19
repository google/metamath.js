include "adantr.mm"
include "adantl.mm"
include "ccase.mm"

theorem ccase2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume ccase2.1: |- ( ( ph /\ ps ) -> ta )
  assume ccase2.2: |- ( ch -> ta )
  assume ccase2.3: |- ( th -> ta )


  assert |- ( ( ( ph \/ ch ) /\ ( ps \/ th ) ) -> ta )

  proof
    wph
    wps
    wch
    wth
    wta
    ccase2.1
    wch
    wta
    wps
    ccase2.2
    adantr
    wth
    wta
    wph
    ccase2.3
    adantl
    wth
    wta
    wch
    ccase2.3
    adantl
    ccase
end
