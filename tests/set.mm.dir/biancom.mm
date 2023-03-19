include "wa.mm"
include "ancom.mm"
include "bitr4i.mm"

theorem biancom
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume biancom.1: |- ( ph <-> ( ch /\ ps ) )


  assert |- ( ph <-> ( ps /\ ch ) )

  proof
    wph
    wch
    wps
    wa
    wps
    wch
    wa
    biancom.1
    wps
    wch
    ancom
    bitr4i
end
