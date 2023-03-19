include "wxo.mm"
include "wa.mm"
include "axorbciffatcxorb.mm"
include "pm3.2i.mm"

theorem mdandyvrx7
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
  assume mdandyvrx7.1: |- ( ph \/_ ze )
  assume mdandyvrx7.2: |- ( ps \/_ si )
  assume mdandyvrx7.3: |- ( ch <-> ps )
  assume mdandyvrx7.4: |- ( th <-> ps )
  assume mdandyvrx7.5: |- ( ta <-> ps )
  assume mdandyvrx7.6: |- ( et <-> ph )


  assert |- ( ( ( ( ch \/_ si ) /\ ( th \/_ si ) ) /\ ( ta \/_ si ) ) /\ ( et \/_ ze ) )

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
    wsi
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
    mdandyvrx7.2
    mdandyvrx7.3
    axorbciffatcxorb
    wps
    wsi
    wth
    mdandyvrx7.2
    mdandyvrx7.4
    axorbciffatcxorb
    pm3.2i
    wps
    wsi
    wta
    mdandyvrx7.2
    mdandyvrx7.5
    axorbciffatcxorb
    pm3.2i
    wph
    wze
    wet
    mdandyvrx7.1
    mdandyvrx7.6
    axorbciffatcxorb
    pm3.2i
end
