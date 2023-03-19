include "wvhc2.mm"
include "wvd1.mm"
include "wa.mm"
include "wi.mm"
include "dfvd2an.mm"
include "mpbi.mm"

theorem dfvd2ani
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume dfvd2ani.1: |- (. (. ph ,. ps ). ->. ch ).


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wph
    wps
    wvhc2
    wch
    wvd1
    wph
    wps
    wa
    wch
    wi
    dfvd2ani.1
    wph
    wps
    wch
    dfvd2an
    mpbi
end
