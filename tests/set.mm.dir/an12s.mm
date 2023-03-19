include "wa.mm"
include "an12.mm"
include "sylbi.mm"

theorem an12s
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume an12s.1: |- ( ( ph /\ ( ps /\ ch ) ) -> th )


  assert |- ( ( ps /\ ( ph /\ ch ) ) -> th )

  proof
    wps
    wph
    wch
    wa
    wa
    wph
    wps
    wch
    wa
    wa
    wth
    wps
    wph
    wch
    an12
    an12s.1
    sylbi
end
