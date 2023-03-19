include "wsb.mm"
include "sbcom2.mm"
include "sbbii.mm"
include "nfv.mm"
include "sbco2.mm"
include "bitri.mm"
include "sbid2v.mm"
include "3bitr3i.mm"

theorem sbco4lem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vv: setvar v

  disjoint v w
  disjoint ph v
  disjoint ph w
  disjoint v x
  disjoint w x
  disjoint v y
  disjoint w y
  assert |- ( [ x / v ] [ y / x ] [ v / y ] ph <-> [ x / w ] [ y / x ] [ w / y ] ph )

  proof
    wph
    vy
    vw
    wsb
    #
    vw
    vv
    wsb
    #
    vx
    vy
    wsb
    #
    vv
    vw
    wsb
    #
    vw
    vx
    wsb
    #
    @1
    vv
    vw
    wsb
    #
    vx
    vy
    wsb
    #
    vw
    vx
    wsb
    wph
    vy
    vv
    wsb
    #
    vx
    vy
    wsb
    #
    vv
    vx
    wsb
    #
    @0
    vx
    vy
    wsb
    #
    vw
    vx
    wsb
    @3
    @6
    vw
    vx
    @1
    vx
    vy
    vv
    vw
    sbcom2
    sbbii
    @4
    @8
    vv
    vw
    wsb
    #
    vw
    vx
    wsb
    @9
    @3
    @11
    vw
    vx
    @2
    @8
    vv
    vw
    @1
    @7
    vx
    vy
    wph
    vy
    vv
    vw
    wph
    vw
    nfv
    sbco2
    sbbii
    sbbii
    sbbii
    @8
    vv
    vx
    vw
    @8
    vw
    nfv
    sbco2
    bitri
    @6
    @10
    vw
    vx
    @5
    @0
    vx
    vy
    @0
    vv
    vw
    sbid2v
    sbbii
    sbbii
    3bitr3i
end
