include "wsb.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "sb6.mm"
include "19.21v.mm"
include "impexp.mm"
include "albii.mm"
include "imbi2i.mm"
include "3bitr4ri.mm"
include "bitri.mm"

theorem 2sb6
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint w y
  assert |- ( [ z / x ] [ w / y ] ph <-> A. x A. y ( ( x = z /\ y = w ) -> ph ) )

  proof
    wph
    vy
    vw
    wsb
    #
    vx
    vz
    wsb
    vx
    vz
    weq
    #
    @0
    wi
    #
    vx
    wal
    @1
    vy
    vw
    weq
    #
    wa
    wph
    wi
    #
    vy
    wal
    #
    vx
    wal
    @0
    vx
    vz
    sb6
    @2
    @5
    vx
    @1
    @3
    wph
    wi
    #
    wi
    #
    vy
    wal
    @1
    @6
    vy
    wal
    #
    wi
    @5
    @2
    @1
    @6
    vy
    19.21v
    @4
    @7
    vy
    @1
    @3
    wph
    impexp
    albii
    @0
    @8
    @1
    wph
    vy
    vw
    sb6
    imbi2i
    3bitr4ri
    albii
    bitri
end
