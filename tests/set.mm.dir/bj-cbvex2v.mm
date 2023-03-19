include "wn.mm"
include "wal.mm"
include "wex.mm"
include "nfn.mm"
include "weq.mm"
include "wa.mm"
include "notbid.mm"
include "bj-cbval2v.mm"
include "notbii.mm"
include "2exnaln.mm"
include "3bitr4i.mm"

theorem bj-cbvex2v
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
    bj-cbval2v.1
    nfn
    wph
    vw
    bj-cbval2v.2
    nfn
    wps
    vx
    bj-cbval2v.3
    nfn
    wps
    vy
    bj-cbval2v.4
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
    bj-cbval2v.5
    notbid
    bj-cbval2v
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
