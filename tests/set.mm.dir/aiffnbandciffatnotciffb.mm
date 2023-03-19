include "wb.mm"
include "wn.mm"
include "bitri.mm"
include "xor3.mm"
include "mpbir.mm"

theorem aiffnbandciffatnotciffb
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vk: setvar k
  let vx: setvar x
  assume aiffnbandciffatnotciffb.1: |- ( ph <-> -. ps )
  assume aiffnbandciffatnotciffb.2: |- ( ch <-> ph )


  assert |- -. ( ch <-> ps )

  proof
    wch
    wps
    wb
    wn
    wch
    wps
    wn
    #
    wb
    wch
    wph
    @0
    aiffnbandciffatnotciffb.2
    aiffnbandciffatnotciffb.1
    bitri
    wch
    wps
    xor3
    mpbir
end
