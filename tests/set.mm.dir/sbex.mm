include "wn.mm"
include "wal.mm"
include "wsb.mm"
include "wex.mm"
include "sbn.mm"
include "sbal.mm"
include "albii.mm"
include "bitri.mm"
include "xchbinx.mm"
include "df-ex.mm"
include "sbbii.mm"
include "3bitr4i.mm"

theorem sbex
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint x z
  assert |- ( [ z / y ] E. x ph <-> E. x [ z / y ] ph )

  proof
    wph
    wn
    #
    vx
    wal
    #
    wn
    #
    vy
    vz
    wsb
    #
    wph
    vy
    vz
    wsb
    #
    wn
    #
    vx
    wal
    #
    wn
    wph
    vx
    wex
    #
    vy
    vz
    wsb
    @4
    vx
    wex
    @3
    @1
    vy
    vz
    wsb
    #
    @6
    @1
    vy
    vz
    sbn
    @8
    @0
    vy
    vz
    wsb
    #
    vx
    wal
    @6
    @0
    vx
    vy
    vz
    sbal
    @9
    @5
    vx
    wph
    vy
    vz
    sbn
    albii
    bitri
    xchbinx
    @7
    @2
    vy
    vz
    wph
    vx
    df-ex
    sbbii
    @4
    vx
    df-ex
    3bitr4i
end
