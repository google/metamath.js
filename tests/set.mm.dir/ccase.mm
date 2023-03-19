include "wo.mm"
include "jaoian.mm"
include "jaodan.mm"

theorem ccase
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume ccase.1: |- ( ( ph /\ ps ) -> ta )
  assume ccase.2: |- ( ( ch /\ ps ) -> ta )
  assume ccase.3: |- ( ( ph /\ th ) -> ta )
  assume ccase.4: |- ( ( ch /\ th ) -> ta )


  assert |- ( ( ( ph \/ ch ) /\ ( ps \/ th ) ) -> ta )

  proof
    wph
    wch
    wo
    wps
    wta
    wth
    wph
    wps
    wta
    wch
    ccase.1
    ccase.2
    jaoian
    wph
    wth
    wta
    wch
    ccase.3
    ccase.4
    jaoian
    jaodan
end
