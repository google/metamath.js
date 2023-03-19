include "wa.mm"
include "wb.mm"
include "adantr.mm"
include "adantl.mm"
include "bitrd.mm"

theorem sylan9bb
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume sylan9bb.1: |- ( ph -> ( ps <-> ch ) )
  assume sylan9bb.2: |- ( th -> ( ch <-> ta ) )


  assert |- ( ( ph /\ th ) -> ( ps <-> ta ) )

  proof
    wph
    wth
    wa
    wps
    wch
    wta
    wph
    wps
    wch
    wb
    wth
    sylan9bb.1
    adantr
    wth
    wch
    wta
    wb
    wph
    sylan9bb.2
    adantl
    bitrd
end
