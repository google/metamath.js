include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wi.mm"
include "wnf.mm"
include "nfv.mm"
include "equcom.mm"
include "nfna1.mm"
include "nf5d.mm"
include "nfxfrd.mm"
include "nf5i.mm"
include "a1i.mm"
include "nfimd.mm"
include "nfald.mm"
include "equsalhw.mm"
include "nfbii.mm"
include "sylib.mm"
include "nf5rd.mm"

theorem dvelimhw
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume dvelimhw.1: |- ( ph -> A. x ph )
  assume dvelimhw.2: |- ( ps -> A. z ps )
  assume dvelimhw.3: |- ( z = y -> ( ph <-> ps ) )
  assume dvelimhw.4: |- ( -. A. x x = y -> ( y = z -> A. x y = z ) )

  disjoint x z
  disjoint y z
  assert |- ( -. A. x x = y -> ( ps -> A. x ps ) )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    wn
    #
    wps
    vx
    @1
    vz
    vy
    weq
    #
    wph
    wi
    #
    vz
    wal
    #
    vx
    wnf
    wps
    vx
    wnf
    @1
    @3
    vx
    vz
    @1
    vz
    nfv
    @1
    @2
    wph
    vx
    @2
    vy
    vz
    weq
    #
    @1
    vx
    vz
    vy
    equcom
    @1
    @5
    vx
    @0
    vx
    nfna1
    dvelimhw.4
    nf5d
    nfxfrd
    wph
    vx
    wnf
    @1
    wph
    vx
    dvelimhw.1
    nf5i
    a1i
    nfimd
    nfald
    @4
    wps
    vx
    wph
    wps
    vz
    vy
    dvelimhw.2
    dvelimhw.3
    equsalhw
    nfbii
    sylib
    nf5rd
end
