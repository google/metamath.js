include "wa.mm"
include "pm5.32i.mm"
include "ancom.mm"
include "3bitr4i.mm"

theorem pm5.32ri
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume pm5.32i.1: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ( ps /\ ph ) <-> ( ch /\ ph ) )

  proof
    wph
    wps
    wa
    wph
    wch
    wa
    wps
    wph
    wa
    wch
    wph
    wa
    wph
    wps
    wch
    pm5.32i.1
    pm5.32i
    wps
    wph
    ancom
    wch
    wph
    ancom
    3bitr4i
end
