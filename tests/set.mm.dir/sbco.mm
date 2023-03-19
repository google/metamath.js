include "wsb.mm"
include "sbcom3.mm"
include "sbid.mm"
include "sbbii.mm"
include "bitri.mm"

theorem sbco
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( [ y / x ] [ x / y ] ph <-> [ y / x ] ph )

  proof
    wph
    vy
    vx
    wsb
    vx
    vy
    wsb
    wph
    vy
    vy
    wsb
    #
    vx
    vy
    wsb
    wph
    vx
    vy
    wsb
    wph
    vy
    vx
    vy
    sbcom3
    @0
    wph
    vx
    vy
    wph
    vy
    sbid
    sbbii
    bitri
end
