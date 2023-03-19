include "sylanb.mm"
include "sylan2b.mm"

theorem syl2anb
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume syl2anb.1: |- ( ph <-> ps )
  assume syl2anb.2: |- ( ta <-> ch )
  assume syl2anb.3: |- ( ( ps /\ ch ) -> th )


  assert |- ( ( ph /\ ta ) -> th )

  proof
    wta
    wph
    wch
    wth
    syl2anb.2
    wph
    wps
    wch
    wth
    syl2anb.1
    syl2anb.3
    sylanb
    sylan2b
end
