include "wxo.mm"
include "wa.mm"
include "axorbciffatcxorb.mm"
include "pm3.2i.mm"

theorem mdandyvrx3
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
  assume mdandyvrx3.1: |- ( ph \/_ ze )
  assume mdandyvrx3.2: |- ( ps \/_ si )
  assume mdandyvrx3.3: |- ( ch <-> ps )
  assume mdandyvrx3.4: |- ( th <-> ps )
  assume mdandyvrx3.5: |- ( ta <-> ph )
  assume mdandyvrx3.6: |- ( et <-> ph )


  assert |- ( ( ( ( ch \/_ si ) /\ ( th \/_ si ) ) /\ ( ta \/_ ze ) ) /\ ( et \/_ ze ) )

  proof
    wch
    wsi
    wxo
    #
    wth
    wsi
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
    wps
    wsi
    wch
    mdandyvrx3.2
    mdandyvrx3.3
    axorbciffatcxorb
    wps
    wsi
    wth
    mdandyvrx3.2
    mdandyvrx3.4
    axorbciffatcxorb
    pm3.2i
    wph
    wze
    wta
    mdandyvrx3.1
    mdandyvrx3.5
    axorbciffatcxorb
    pm3.2i
    wph
    wze
    wet
    mdandyvrx3.1
    mdandyvrx3.6
    axorbciffatcxorb
    pm3.2i
end
