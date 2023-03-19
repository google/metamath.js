include "wnan.mm"
include "nic-isw1.mm"
include "nic-imp.mm"
include "nic-mp.mm"

theorem nic-ich
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume nic-ich.1: |- ( ph -/\ ( ps -/\ ps ) )
  assume nic-ich.2: |- ( ps -/\ ( ch -/\ ch ) )


  assert |- ( ph -/\ ( ch -/\ ch ) )

  proof
    wch
    wch
    wnan
    #
    wps
    wnan
    wph
    @0
    wnan
    #
    @1
    @0
    wps
    nic-ich.2
    nic-isw1
    wph
    wps
    wps
    @0
    nic-ich.1
    nic-imp
    nic-mp
end
