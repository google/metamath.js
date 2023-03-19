include "wsb.mm"
include "sbcom3.mm"
include "sbid.mm"
include "sbbii.mm"
include "bitr3i.mm"

theorem sbidm
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( [ y / x ] [ y / x ] ph <-> [ y / x ] ph )

  proof
    wph
    vx
    vy
    wsb
    #
    vx
    vy
    wsb
    wph
    vx
    vx
    wsb
    #
    vx
    vy
    wsb
    @0
    wph
    vx
    vx
    vy
    sbcom3
    @1
    wph
    vx
    vy
    wph
    vx
    sbid
    sbbii
    bitr3i
end
