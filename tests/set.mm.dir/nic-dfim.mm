include "wnan.mm"
include "wi.mm"
include "wb.mm"
include "nanim.mm"
include "bicomi.mm"
include "nanbi.mm"
include "mpbi.mm"

theorem nic-dfim
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ( ph -/\ ( ps -/\ ps ) ) -/\ ( ph -> ps ) ) -/\ ( ( ( ph -/\ ( ps -/\ ps ) ) -/\ ( ph -/\ ( ps -/\ ps ) ) ) -/\ ( ( ph -> ps ) -/\ ( ph -> ps ) ) ) )

  proof
    wph
    wps
    wps
    wnan
    wnan
    #
    wph
    wps
    wi
    #
    wb
    @0
    @1
    wnan
    @0
    @0
    wnan
    @1
    @1
    wnan
    wnan
    wnan
    @1
    @0
    wph
    wps
    nanim
    bicomi
    @0
    @1
    nanbi
    mpbi
end
