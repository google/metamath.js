include "wb.mm"
include "sylan9bb.mm"
include "ancoms.mm"

theorem sylan9bbr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume sylan9bbr.1: |- ( ph -> ( ps <-> ch ) )
  assume sylan9bbr.2: |- ( th -> ( ch <-> ta ) )


  assert |- ( ( th /\ ph ) -> ( ps <-> ta ) )

  proof
    wph
    wth
    wps
    wta
    wb
    wph
    wps
    wch
    wth
    wta
    sylan9bbr.1
    sylan9bbr.2
    sylan9bb
    ancoms
end
