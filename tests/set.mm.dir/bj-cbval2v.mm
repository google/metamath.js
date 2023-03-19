include "wal.mm"
include "nfal.mm"
include "weq.mm"
include "wi.mm"
include "nfv.mm"
include "nfim.mm"
include "wb.mm"
include "expcom.mm"
include "pm5.74d.mm"
include "cbvalv1.mm"
include "19.21v.mm"
include "3bitr3i.mm"
include "pm5.74ri.mm"

theorem bj-cbval2v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume bj-cbval2v.1: |- F/ z ph
  assume bj-cbval2v.2: |- F/ w ph
  assume bj-cbval2v.3: |- F/ x ps
  assume bj-cbval2v.4: |- F/ y ps
  assume bj-cbval2v.5: |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) )

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  assert |- ( A. x A. y ph <-> A. z A. w ps )

  proof
    wph
    vy
    wal
    #
    wps
    vw
    wal
    #
    vx
    vz
    wph
    vz
    vy
    bj-cbval2v.1
    nfal
    wps
    vx
    vw
    bj-cbval2v.3
    nfal
    vx
    vz
    weq
    #
    @0
    @1
    @2
    wph
    wi
    #
    vy
    wal
    @2
    wps
    wi
    #
    vw
    wal
    @2
    @0
    wi
    @2
    @1
    wi
    @3
    @4
    vy
    vw
    @2
    wph
    vw
    @2
    vw
    nfv
    bj-cbval2v.2
    nfim
    @2
    wps
    vy
    @2
    vy
    nfv
    bj-cbval2v.4
    nfim
    vy
    vw
    weq
    #
    @2
    wph
    wps
    @2
    @5
    wph
    wps
    wb
    bj-cbval2v.5
    expcom
    pm5.74d
    cbvalv1
    @2
    wph
    vy
    19.21v
    @2
    wps
    vw
    19.21v
    3bitr3i
    pm5.74ri
    cbvalv1
end
