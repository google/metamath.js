include "ex.mm"
include "sylc.mm"

theorem syl2anc
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
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
