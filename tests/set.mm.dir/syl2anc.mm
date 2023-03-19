include "ex.mm"
include "sylc.mm"

theorem syl2anc
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume syl2anc.1: |- ( ph -> ps )
  assume syl2anc.2: |- ( ph -> ch )
  assume syl2anc.3: |- ( ( ps /\ ch ) -> th )


  assert |- ( ph -> th )

  proof
    wph
    wps
    wch
    wth
    syl2anc.1
    syl2anc.2
    wps
    wch
    wth
    syl2anc.3
    ex
    sylc
end
