include "w3a.mm"
include "3jca.mm"
include "sylibr.mm"

theorem syl3anbrc
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume syl3anbrc.1: |- ( ph -> ps )
  assume syl3anbrc.2: |- ( ph -> ch )
  assume syl3anbrc.3: |- ( ph -> th )
  assume syl3anbrc.4: |- ( ta <-> ( ps /\ ch /\ th ) )


  assert |- ( ph -> ta )

  proof
    wph
    wps
    wch
    wth
    w3a
    wta
    wph
    wps
    wch
    wth
    syl3anbrc.1
    syl3anbrc.2
    syl3anbrc.3
    3jca
    syl3anbrc.4
    sylibr
end
