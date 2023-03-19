include "weu.mm"
include "wsb.mm"
include "sb8eu.mm"
include "sbie.mm"
include "eubii.mm"
include "bitri.mm"

theorem cbveu
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume cbveu.1: |- F/ y ph
  assume cbveu.2: |- F/ x ps
  assume cbveu.3: |- ( x = y -> ( ph <-> ps ) )


  assert |- ( E! x ph <-> E! y ps )

  proof
    wph
    vx
    weu
    wph
    vx
    vy
    wsb
    #
    vy
    weu
    wps
    vy
    weu
    wph
    vx
    vy
    cbveu.1
    sb8eu
    @0
    wps
    vy
    wph
    wps
    vx
    vy
    cbveu.2
    cbveu.3
    sbie
    eubii
    bitri
end
