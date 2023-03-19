include "wa.mm"
include "wb.mm"
include "adantr.mm"
include "adantl.mm"
include "bibi12d.mm"

theorem bi2bian9
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume bi2an9.1: |- ( ph -> ( ps <-> ch ) )
  assume bi2an9.2: |- ( th -> ( ta <-> et ) )


  assert |- ( ( ph /\ th ) -> ( ( ps <-> ta ) <-> ( ch <-> et ) ) )

  proof
    wph
    wth
    wa
    wps
    wch
    wta
    wet
    wph
    wps
    wch
    wb
    wth
    bi2an9.1
    adantr
    wth
    wta
    wet
    wb
    wph
    bi2an9.2
    adantl
    bibi12d
end
