include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "wsb.mm"
include "wmo.mm"
include "sbex.mm"
include "nfv.mm"
include "sblim.mm"
include "sbalv.mm"
include "exbii.mm"
include "bitri.mm"
include "mo2v.mm"
include "sbbii.mm"
include "3bitr4i.mm"

theorem sbmo
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x z
  disjoint y z
  disjoint w x
  disjoint w z
  disjoint w y
  disjoint ph w
  assert |- ( [ y / x ] E* z ph <-> E* z [ y / x ] ph )

  proof
    wph
    vz
    vw
    weq
    #
    wi
    #
    vz
    wal
    #
    vw
    wex
    #
    vx
    vy
    wsb
    #
    wph
    vx
    vy
    wsb
    #
    @0
    wi
    #
    vz
    wal
    #
    vw
    wex
    #
    wph
    vz
    wmo
    #
    vx
    vy
    wsb
    @5
    vz
    wmo
    @4
    @2
    vx
    vy
    wsb
    #
    vw
    wex
    @8
    @2
    vw
    vx
    vy
    sbex
    @10
    @7
    vw
    @1
    @6
    vx
    vy
    vz
    wph
    @0
    vx
    vy
    @0
    vx
    nfv
    sblim
    sbalv
    exbii
    bitri
    @9
    @3
    vx
    vy
    wph
    vz
    vw
    mo2v
    sbbii
    @5
    vz
    vw
    mo2v
    3bitr4i
end
