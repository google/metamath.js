include "syl2anbr.mm"
include "anidms.mm"

theorem sylancbr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume sylancbr.1: |- ( ps <-> ph )
  assume sylancbr.2: |- ( ch <-> ph )
  assume sylancbr.3: |- ( ( ps /\ ch ) -> th )


  assert |- ( ph -> th )

  proof
    wph
    wth
    wph
    wps
    wch
    wth
    wph
    sylancbr.1
    sylancbr.2
    sylancbr.3
    syl2anbr
    anidms
end
