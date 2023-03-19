include "wnan.mm"
include "nic-swap.mm"
include "nic-imp.mm"
include "nic-mp.mm"
include "nic-isw1.mm"

theorem nic-isw2
  let wph: wff ph
  let wps: wff ps
  let wth: wff th
  assume nic-isw2.1: |- ( ps -/\ ( th -/\ ph ) )


  assert |- ( ps -/\ ( ph -/\ th ) )

  proof
    wps
    wph
    wth
    wnan
    #
    wps
    wth
    wph
    wnan
    #
    wnan
    @0
    wps
    wnan
    #
    @2
    nic-isw2.1
    @0
    @1
    @1
    wps
    wth
    wph
    nic-swap
    nic-imp
    nic-mp
    nic-isw1
end
