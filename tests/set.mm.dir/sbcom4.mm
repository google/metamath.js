include "wsb.mm"
include "nfv.mm"
include "sbf.mm"
include "sbbii.mm"
include "bitri.mm"
include "3bitr4i.mm"

theorem sbcom4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint w x
  disjoint w z
  assert |- ( [ w / x ] [ y / z ] ph <-> [ y / x ] [ w / z ] ph )

  proof
    wph
    vx
    vw
    wsb
    wph
    wph
    vz
    vy
    wsb
    #
    vx
    vw
    wsb
    wph
    vz
    vw
    wsb
    #
    vx
    vy
    wsb
    #
    wph
    vx
    vw
    wph
    vx
    nfv
    #
    sbf
    @0
    wph
    vx
    vw
    wph
    vz
    vy
    wph
    vz
    nfv
    #
    sbf
    sbbii
    @2
    wph
    vx
    vy
    wsb
    wph
    @1
    wph
    vx
    vy
    wph
    vz
    vw
    @4
    sbf
    sbbii
    wph
    vx
    vy
    @3
    sbf
    bitri
    3bitr4i
end
