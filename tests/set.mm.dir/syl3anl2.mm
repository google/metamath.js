include "w3a.mm"
include "wi.mm"
include "ex.mm"
include "syl3an2.mm"
include "imp.mm"

theorem syl3anl2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume syl3anl2.1: |- ( ph -> ch )
  assume syl3anl2.2: |- ( ( ( ps /\ ch /\ th ) /\ ta ) -> et )


  assert |- ( ( ( ps /\ ph /\ th ) /\ ta ) -> et )

  proof
    wps
    wph
    wth
    w3a
    wta
    wet
    wph
    wps
    wch
    wth
    wta
    wet
    wi
    syl3anl2.1
    wps
    wch
    wth
    w3a
    wta
    wet
    syl3anl2.2
    ex
    syl3an2
    imp
end
