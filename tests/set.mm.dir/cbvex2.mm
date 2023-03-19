include "wn.mm"
include "wal.mm"
include "wex.mm"
include "nfn.mm"
include "weq.mm"
include "wa.mm"
include "notbid.mm"
include "cbval2.mm"
include "notbii.mm"
include "2exnaln.mm"
include "3bitr4i.mm"

theorem cbvex2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume cbval2.1: |- F/ z ph
  assume cbval2.2: |- F/ w ph
  assume cbval2.3: |- F/ x ps
  assume cbval2.4: |- F/ y ps
  assume cbval2.5: |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) )

  disjoint x y
  disjoint y z
  disjoint w x
  disjoint w z
  assert |- ( E. x E. y ph <-> E. z E. w ps )

  proof
    wph
    wn
    #
    vy
    wal
    vx
    wal
    #
    wn
    wps
    wn
    #
    vw
    wal
    vz
    wal
    #
    wn
    wph
    vy
    wex
    vx
    wex
    wps
    vw
    wex
    vz
    wex
    @1
    @3
    @0
    @2
    vx
    vy
    vz
    vw
    wph
    vz
    cbval2.1
    nfn
    wph
    vw
    cbval2.2
    nfn
    wps
    vx
    cbval2.3
    nfn
    wps
    vy
    cbval2.4
    nfn
    vx
    vz
    weq
    vy
    vw
    weq
    wa
    wph
    wps
    cbval2.5
    notbid
    cbval2
    notbii
    wph
    vx
    vy
    2exnaln
    wps
    vz
    vw
    2exnaln
    3bitr4i
end
