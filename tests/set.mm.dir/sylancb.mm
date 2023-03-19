include "syl2anb.mm"
include "anidms.mm"

theorem sylancb
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume sylancb.1: |- ( ph <-> ps )
  assume sylancb.2: |- ( ph <-> ch )
  assume sylancb.3: |- ( ( ps /\ ch ) -> th )


  assert |- ( ph -> th )

  proof
    wph
    wth
    wph
    wps
    wch
    wth
    wph
    sylancb.1
    sylancb.2
    sylancb.3
    syl2anb
    anidms
end
