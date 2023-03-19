include "wtru.mm"
include "w3a.mm"
include "wa.mm"
include "3anass.mm"
include "simpr.mm"
include "jctl.mm"
include "impbii.mm"
include "truan.mm"
include "3bitri.mm"
include "syl3an2.mm"
include "syl3an3.mm"
include "sylbir.mm"

theorem eel0T1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume eel0T1.1: |- ph
  assume eel0T1.2: |- ( T. -> ps )
  assume eel0T1.3: |- ( ch -> th )
  assume eel0T1.4: |- ( ( ph /\ ps /\ th ) -> ta )


  assert |- ( ch -> ta )

  proof
    wch
    wph
    wtru
    wch
    w3a
    #
    wta
    @0
    wph
    wtru
    wch
    wa
    #
    wa
    #
    @1
    wch
    wph
    wtru
    wch
    3anass
    @2
    @1
    wph
    @1
    simpr
    @1
    wph
    eel0T1.1
    jctl
    impbii
    wch
    truan
    3bitri
    wch
    wph
    wtru
    wth
    wta
    eel0T1.3
    wtru
    wph
    wps
    wth
    wta
    eel0T1.2
    eel0T1.4
    syl3an2
    syl3an3
    sylbir
end
