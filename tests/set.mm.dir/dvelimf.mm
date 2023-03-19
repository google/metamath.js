include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wn.mm"
include "equsal.mm"
include "bicomi.mm"
include "nfnae.mm"
include "wa.mm"
include "wnf.mm"
include "nfeqf.mm"
include "ancoms.mm"
include "a1i.mm"
include "nfimd.mm"
include "nfald2.mm"
include "nfxfrd.mm"

theorem dvelimf
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume dvelimf.1: |- F/ x ph
  assume dvelimf.2: |- F/ z ps
  assume dvelimf.3: |- ( z = y -> ( ph <-> ps ) )


  assert |- ( -. A. x x = y -> F/ x ps )

  proof
    wps
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
    vy
    weq
    vx
    wal
    wn
    #
    vx
    @2
    wps
    wph
    wps
    vz
    vy
    dvelimf.2
    dvelimf.3
    equsal
    bicomi
    @3
    @1
    vx
    vz
    vx
    vy
    vz
    nfnae
    @3
    vx
    vz
    weq
    vx
    wal
    wn
    #
    wa
    #
    @0
    wph
    vx
    @4
    @3
    @0
    vx
    wnf
    vz
    vy
    vx
    nfeqf
    ancoms
    wph
    vx
    wnf
    @5
    dvelimf.1
    a1i
    nfimd
    nfald2
    nfxfrd
end
