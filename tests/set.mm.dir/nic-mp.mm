include "wnan.mm"
include "wa.mm"
include "wi.mm"
include "nannan.mm"
include "mpbi.mm"
include "simprd.mm"
include "ax-mp.mm"

theorem nic-mp
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume nic-jmin: |- ph
  assume nic-jmaj: |- ( ph -/\ ( ch -/\ ps ) )


  assert |- ps

  proof
    wph
    wps
    nic-jmin
    wph
    wch
    wps
    wph
    wch
    wps
    wnan
    wnan
    wph
    wch
    wps
    wa
    wi
    nic-jmaj
    wph
    wps
    wch
    nannan
    mpbi
    simprd
    ax-mp
end
