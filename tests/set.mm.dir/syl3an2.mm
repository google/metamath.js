include "wi.mm"
include "3exp.mm"
include "syl5.mm"
include "3imp.mm"

theorem syl3an2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume syl3an2.1: |- ( ph -> ch )
  assume syl3an2.2: |- ( ( ps /\ ch /\ th ) -> ta )


  assert |- ( ( ps /\ ph /\ th ) -> ta )

  proof
    wps
    wph
    wth
    wta
    wph
    wch
    wps
    wth
    wta
    wi
    syl3an2.1
    wps
    wch
    wth
    wta
    syl3an2.2
    3exp
    syl5
    3imp
end
