include "wnan.mm"
include "nic-id.mm"
include "nic-iimp1.mm"
include "nic-isw2.mm"
include "nic-idel.mm"

theorem nic-bi1
  let wph: wff ph
  let wps: wff ps
  assume nic-bi1.1: |- ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph ) -/\ ( ps -/\ ps ) ) )


  assert |- ( ph -/\ ( ps -/\ ps ) )

  proof
    wph
    wph
    wps
    wps
    wph
    wph
    wph
    wps
    wnan
    wps
    wps
    wnan
    wph
    wph
    wnan
    wph
    nic-bi1.1
    wph
    nic-id
    nic-iimp1
    nic-isw2
    nic-idel
end
