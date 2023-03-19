include "wex.mm"
include "wsb.mm"
include "weq.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "2sb8e.mm"
include "2sb6.mm"
include "2exbii.mm"
include "bitri.mm"

theorem 2exsb
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint ph z
  disjoint ph w
  assert |- ( E. x E. y ph <-> E. z E. w A. x A. y ( ( x = z /\ y = w ) -> ph ) )

  proof
    wph
    vy
    wex
    vx
    wex
    wph
    vy
    vw
    wsb
    vx
    vz
    wsb
    #
    vw
    wex
    vz
    wex
    vx
    vz
    weq
    vy
    vw
    weq
    wa
    wph
    wi
    vy
    wal
    vx
    wal
    #
    vw
    wex
    vz
    wex
    wph
    vx
    vy
    vz
    vw
    2sb8e
    @0
    @1
    vz
    vw
    wph
    vx
    vy
    vz
    vw
    2sb6
    2exbii
    bitri
end
