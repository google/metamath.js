include "a1i.mm"
include "syl2anc.mm"

theorem sylancr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume sylancr.1: |- ps
  assume sylancr.2: |- ( ph -> ch )
  assume sylancr.3: |- ( ( ps /\ ch ) -> th )


  assert |- ( ph -> th )

  proof
    wph
    wps
    wch
    wth
    wps
    wph
    sylancr.1
    a1i
    sylancr.2
    sylancr.3
    syl2anc
end
