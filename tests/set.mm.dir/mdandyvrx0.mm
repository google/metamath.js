include "wxo.mm"
include "wa.mm"
include "axorbciffatcxorb.mm"
include "pm3.2i.mm"

theorem mdandyvrx0
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
  let vk: setvar k
  let vx: setvar x
  assume mdandyvrx0.1: |- ( ph \/_ ze )
  assume mdandyvrx0.2: |- ( ps \/_ si )
  assume mdandyvrx0.3: |- ( ch <-> ph )
  assume mdandyvrx0.4: |- ( th <-> ph )
  assume mdandyvrx0.5: |- ( ta <-> ph )
  assume mdandyvrx0.6: |- ( et <-> ph )


  assert |- ( ( ( ( ch \/_ ze ) /\ ( th \/_ ze ) ) /\ ( ta \/_ ze ) ) /\ ( et \/_ ze ) )

  proof
    wch
    wze
    wxo
    #
    wth
    wze
    wxo
    #
    wa
    #
    wta
    wze
    wxo
    #
    wa
    wet
    wze
    wxo
    @2
    @3
    @0
    @1
    wph
    wze
    wch
    mdandyvrx0.1
    mdandyvrx0.3
    axorbciffatcxorb
    wph
    wze
    wth
    mdandyvrx0.1
    mdandyvrx0.4
    axorbciffatcxorb
    pm3.2i
    wph
    wze
    wta
    mdandyvrx0.1
    mdandyvrx0.5
    axorbciffatcxorb
    pm3.2i
    wph
    wze
    wet
    mdandyvrx0.1
    mdandyvrx0.6
    axorbciffatcxorb
    pm3.2i
end
