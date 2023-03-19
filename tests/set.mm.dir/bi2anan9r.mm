include "wa.mm"
include "wb.mm"
include "bi2anan9.mm"
include "ancoms.mm"

theorem bi2anan9r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume bi2an9.1: |- ( ph -> ( ps <-> ch ) )
  assume bi2an9.2: |- ( th -> ( ta <-> et ) )


  assert |- ( ( th /\ ph ) -> ( ( ps /\ ta ) <-> ( ch /\ et ) ) )

  proof
    wph
    wth
    wps
    wta
    wa
    wch
    wet
    wa
    wb
    wph
    wps
    wch
    wth
    wta
    wet
    bi2an9.1
    bi2an9.2
    bi2anan9
    ancoms
end
