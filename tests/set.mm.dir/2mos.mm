include "weq.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "wsb.mm"
include "2mo.mm"
include "nfv.mm"
include "sbiedv.mm"
include "sbie.mm"
include "anbi2i.mm"
include "imbi1i.mm"
include "2albii.mm"
include "bitri.mm"

theorem 2mos
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume 2mos.1: |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) )

  disjoint w z
  disjoint ph z
  disjoint ph w
  disjoint x y
  disjoint ps x
  disjoint ps y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  assert |- ( E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) <-> A. x A. y A. z A. w ( ( ph /\ ps ) -> ( x = z /\ y = w ) ) )

  proof
    wph
    vx
    vz
    weq
    #
    vy
    vw
    weq
    wa
    #
    wi
    vy
    wal
    vx
    wal
    vw
    wex
    vz
    wex
    wph
    wph
    vy
    vw
    wsb
    #
    vx
    vz
    wsb
    #
    wa
    #
    @1
    wi
    #
    vw
    wal
    vz
    wal
    #
    vy
    wal
    vx
    wal
    wph
    wps
    wa
    #
    @1
    wi
    #
    vw
    wal
    vz
    wal
    #
    vy
    wal
    vx
    wal
    wph
    vx
    vy
    vz
    vw
    2mo
    @6
    @9
    vx
    vy
    @5
    @8
    vz
    vw
    @4
    @7
    @1
    @3
    wps
    wph
    @2
    wps
    vx
    vz
    wps
    vx
    nfv
    @0
    wph
    wps
    vy
    vw
    2mos.1
    sbiedv
    sbie
    anbi2i
    imbi1i
    2albii
    2albii
    bitri
end
