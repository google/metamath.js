include "bicomi.mm"
include "syl3anb.mm"

theorem syl3anbr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  assume syl3anbr.1: |- ( ps <-> ph )
  assume syl3anbr.2: |- ( th <-> ch )
  assume syl3anbr.3: |- ( et <-> ta )
  assume syl3anbr.4: |- ( ( ps /\ th /\ et ) -> ze )


  assert |- ( ( ph /\ ch /\ ta ) -> ze )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    wze
    wps
    wph
    syl3anbr.1
    bicomi
    wth
    wch
    syl3anbr.2
    bicomi
    wet
    wta
    syl3anbr.3
    bicomi
    syl3anbr.4
    syl3anb
end
