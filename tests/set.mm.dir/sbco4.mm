include "wsb.mm"
include "sbcom2.mm"
include "nfv.mm"
include "sbco2.mm"
include "sbbii.mm"
include "bitr3i.mm"
include "sbco4lem.mm"
include "3bitri.mm"

theorem sbco4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t

  disjoint u v
  disjoint ph u
  disjoint ph v
  disjoint u x
  disjoint v x
  disjoint u y
  disjoint v y
  disjoint ph w
  disjoint w x
  disjoint w y
  disjoint t u
  disjoint t v
  disjoint ph t
  disjoint t x
  disjoint t y
  disjoint t w
  assert |- ( [ y / u ] [ x / v ] [ u / x ] [ v / y ] ph <-> [ x / w ] [ y / x ] [ w / y ] ph )

  proof
    wph
    vy
    vv
    wsb
    #
    vx
    vu
    wsb
    #
    vv
    vx
    wsb
    vu
    vy
    wsb
    #
    @0
    vx
    vy
    wsb
    #
    vv
    vx
    wsb
    #
    wph
    vy
    vt
    wsb
    vx
    vy
    wsb
    vt
    vx
    wsb
    wph
    vy
    vw
    wsb
    vx
    vy
    wsb
    vw
    vx
    wsb
    @2
    @1
    vu
    vy
    wsb
    #
    vv
    vx
    wsb
    @4
    @1
    vu
    vy
    vv
    vx
    sbcom2
    @5
    @3
    vv
    vx
    @0
    vx
    vy
    vu
    @0
    vu
    nfv
    sbco2
    sbbii
    bitr3i
    wph
    vx
    vy
    vt
    vv
    sbco4lem
    wph
    vx
    vy
    vw
    vt
    sbco4lem
    3bitri
end
