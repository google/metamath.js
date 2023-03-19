include "sylanbr.mm"
include "sylan2br.mm"

theorem syl2anbr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume syl2anbr.1: |- ( ps <-> ph )
  assume syl2anbr.2: |- ( ch <-> ta )
  assume syl2anbr.3: |- ( ( ps /\ ch ) -> th )


  assert |- ( ( ph /\ ta ) -> th )

  proof
    wta
    wph
    wch
    wth
    syl2anbr.2
    wph
    wps
    wch
    wth
    syl2anbr.1
    syl2anbr.3
    sylanbr
    sylan2br
end
