include "wa.mm"
include "ancom.mm"
include "sylib.mm"

theorem ancomd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume ancomd.1: |- ( ph -> ( ps /\ ch ) )


  assert |- ( ph -> ( ch /\ ps ) )

  proof
    wph
    wps
    wch
    wa
    wch
    wps
    wa
    ancomd.1
    wps
    wch
    ancom
    sylib
end
