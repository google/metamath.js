include "wb.mm"
include "wi.mm"
include "wa.mm"
include "pm5.32.mm"
include "mpbi.mm"

theorem pm5.32i
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume pm5.32i.1: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ( ph /\ ps ) <-> ( ph /\ ch ) )

  proof
    wph
    wps
    wch
    wb
    wi
    wph
    wps
    wa
    wph
    wch
    wa
    wb
    pm5.32i.1
    wph
    wps
    wch
    pm5.32
    mpbi
end
