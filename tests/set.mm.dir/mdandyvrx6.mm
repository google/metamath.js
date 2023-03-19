include "wxo.mm"
include "wa.mm"
include "axorbciffatcxorb.mm"
include "pm3.2i.mm"

theorem mdandyvrx6
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
  assume mdandyvrx6.1: |- ( ph \/_ ze )
  assume mdandyvrx6.2: |- ( ps \/_ si )
  assume mdandyvrx6.3: |- ( ch <-> ph )
  assume mdandyvrx6.4: |- ( th <-> ps )
  assume mdandyvrx6.5: |- ( ta <-> ps )
  assume mdandyvrx6.6: |- ( et <-> ph )


  assert |- ( ( ( ( ch \/_ ze ) /\ ( th \/_ si ) ) /\ ( ta \/_ si ) ) /\ ( et \/_ ze ) )

  proof
    wch
    wze
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
    wph
    wze
    wch
    mdandyvrx6.1
    mdandyvrx6.3
    axorbciffatcxorb
    wps
    wsi
    wth
    mdandyvrx6.2
    mdandyvrx6.4
    axorbciffatcxorb
    pm3.2i
    wps
    wsi
    wta
    mdandyvrx6.2
    mdandyvrx6.5
    axorbciffatcxorb
    pm3.2i
    wph
    wze
    wet
    mdandyvrx6.1
    mdandyvrx6.6
    axorbciffatcxorb
    pm3.2i
end
