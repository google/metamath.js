include "sylan2i.mm"
include "sylani.mm"

theorem syl2ani
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume syl2ani.1: |- ( ph -> ch )
  assume syl2ani.2: |- ( et -> th )
  assume syl2ani.3: |- ( ps -> ( ( ch /\ th ) -> ta ) )


  assert |- ( ps -> ( ( ph /\ et ) -> ta ) )

  proof
    wph
    wps
    wch
    wet
    wta
    syl2ani.1
    wet
    wps
    wch
    wth
    wta
    syl2ani.2
    syl2ani.3
    sylan2i
    sylani
end
