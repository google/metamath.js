include "wal.mm"
include "wi.mm"
include "wsb.mm"
include "wnf.mm"
include "sbim.mm"
include "sbal.mm"
include "imbi2i.mm"
include "bitri.mm"
include "albii.mm"
include "nf5.mm"
include "sbbii.mm"
include "3bitr4i.mm"

theorem bj-sbnf
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint x z
  assert |- ( [ z / y ] F/ x ph <-> F/ x [ z / y ] ph )

  proof
    wph
    wph
    vx
    wal
    #
    wi
    #
    vy
    vz
    wsb
    #
    vx
    wal
    #
    wph
    vy
    vz
    wsb
    #
    @4
    vx
    wal
    #
    wi
    #
    vx
    wal
    wph
    vx
    wnf
    #
    vy
    vz
    wsb
    #
    @4
    vx
    wnf
    @2
    @6
    vx
    @2
    @4
    @0
    vy
    vz
    wsb
    #
    wi
    @6
    wph
    @0
    vy
    vz
    sbim
    @9
    @5
    @4
    wph
    vx
    vy
    vz
    sbal
    imbi2i
    bitri
    albii
    @8
    @1
    vx
    wal
    #
    vy
    vz
    wsb
    @3
    @7
    @10
    vy
    vz
    wph
    vx
    nf5
    sbbii
    @1
    vx
    vy
    vz
    sbal
    bitri
    @4
    vx
    nf5
    3bitr4i
end
