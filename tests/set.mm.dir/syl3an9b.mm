include "wb.mm"
include "wa.mm"
include "sylan9bb.mm"
include "3impa.mm"

theorem syl3an9b
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  assume syl3an9b.1: |- ( ph -> ( ps <-> ch ) )
  assume syl3an9b.2: |- ( th -> ( ch <-> ta ) )
  assume syl3an9b.3: |- ( et -> ( ta <-> ze ) )


  assert |- ( ( ph /\ th /\ et ) -> ( ps <-> ze ) )

  proof
    wph
    wth
    wet
    wps
    wze
    wb
    wph
    wth
    wa
    wps
    wta
    wet
    wze
    wph
    wps
    wch
    wth
    wta
    syl3an9b.1
    syl3an9b.2
    sylan9bb
    syl3an9b.3
    sylan9bb
    3impa
end
