include "wnan.mm"
include "nic-id.mm"
include "nic-isw1.mm"
include "nic-imp.mm"
include "nic-mp.mm"

theorem nic-idel
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume nic-idel.1: |- ( ph -/\ ( ch -/\ ps ) )


  assert |- ( ph -/\ ( ch -/\ ch ) )

  proof
    wch
    wch
    wnan
    #
    wch
    wnan
    wph
    @0
    wnan
    #
    @1
    @0
    wch
    wch
    nic-id
    nic-isw1
    wph
    wps
    wch
    @0
    nic-idel.1
    nic-imp
    nic-mp
end
