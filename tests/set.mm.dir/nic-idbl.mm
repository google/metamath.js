include "wnan.mm"
include "nic-imp.mm"
include "nic-ich.mm"

theorem nic-idbl
  let wph: wff ph
  let wps: wff ps
  assume nic-idbl.1: |- ( ph -/\ ( ps -/\ ps ) )


  assert |- ( ( ps -/\ ps ) -/\ ( ( ph -/\ ph ) -/\ ( ph -/\ ph ) ) )

  proof
    wps
    wps
    wnan
    wph
    wps
    wnan
    wph
    wph
    wnan
    wph
    wps
    wps
    wps
    nic-idbl.1
    nic-imp
    wph
    wps
    wps
    wph
    nic-idbl.1
    nic-imp
    nic-ich
end
