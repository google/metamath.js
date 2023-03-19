include "wa.mm"
include "anbi1d.mm"
include "anbi2d.mm"
include "sylan9bb.mm"

theorem bi2anan9
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume bi2an9.1: |- ( ph -> ( ps <-> ch ) )
  assume bi2an9.2: |- ( th -> ( ta <-> et ) )


  assert |- ( ( ph /\ th ) -> ( ( ps /\ ta ) <-> ( ch /\ et ) ) )

  proof
    wph
    wps
    wta
    wa
    wch
    wta
    wa
    wth
    wch
    wet
    wa
    wph
    wps
    wch
    wta
    bi2an9.1
    anbi1d
    wth
    wta
    wet
    wch
    bi2an9.2
    anbi2d
    sylan9bb
end
