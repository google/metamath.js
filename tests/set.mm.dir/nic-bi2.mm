include "wnan.mm"
include "nic-isw2.mm"
include "nic-id.mm"
include "nic-iimp1.mm"
include "nic-idel.mm"

theorem nic-bi2
  let wph: wff ph
  let wps: wff ps
  assume nic-bi2.1: |- ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph ) -/\ ( ps -/\ ps ) ) )


  assert |- ( ps -/\ ( ph -/\ ph ) )

  proof
    wps
    wps
    wph
    wph
    wps
    wnan
    #
    wph
    wph
    wnan
    #
    wps
    wps
    wnan
    #
    wps
    @2
    @0
    @1
    nic-bi2.1
    nic-isw2
    wps
    nic-id
    nic-iimp1
    nic-idel
end
