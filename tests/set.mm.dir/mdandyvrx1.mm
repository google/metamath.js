include "wxo.mm"
include "wa.mm"
include "axorbciffatcxorb.mm"
include "pm3.2i.mm"

theorem mdandyvrx1
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
  assume mdandyvrx1.1: |- ( ph \/_ ze )
  assume mdandyvrx1.2: |- ( ps \/_ si )
  assume mdandyvrx1.3: |- ( ch <-> ps )
  assume mdandyvrx1.4: |- ( th <-> ph )
  assume mdandyvrx1.5: |- ( ta <-> ph )
  assume mdandyvrx1.6: |- ( et <-> ph )


  assert |- ( ( ( ( ch \/_ si ) /\ ( th \/_ ze ) ) /\ ( ta \/_ ze ) ) /\ ( et \/_ ze ) )

  proof
    wch
    wsi
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
    wps
    wsi
    wch
    mdandyvrx1.2
    mdandyvrx1.3
    axorbciffatcxorb
    wph
    wze
    wth
    mdandyvrx1.1
    mdandyvrx1.4
    axorbciffatcxorb
    pm3.2i
    wph
    wze
    wta
    mdandyvrx1.1
    mdandyvrx1.5
    axorbciffatcxorb
    pm3.2i
    wph
    wze
    wet
    mdandyvrx1.1
    mdandyvrx1.6
    axorbciffatcxorb
    pm3.2i
end
