include "wmo.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "mo2v.mm"
include "wn.mm"
include "wnf.mm"
include "nfeqf1.mm"
include "naecoms.mm"
include "syl.mm"
include "nfimd.mm"
include "nfald.mm"
include "wb.mm"
include "wa.mm"
include "nfnae.mm"
include "nfeqf2.mm"
include "nfan1.mm"
include "equequ2.mm"
include "imbi2d.mm"
include "adantl.mm"
include "albid.mm"
include "sylan.mm"
include "ex.mm"
include "cbvexd.mm"
include "syl5bb.mm"

theorem wl-mo2df
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  assume wl-mo2df.1: |- F/ x ph
  assume wl-mo2df.2: |- F/ y ph
  assume wl-mo2df.3: |- ( ph -> -. A. x x = y )
  assume wl-mo2df.4: |- ( ph -> F/ y ps )


  assert |- ( ph -> ( E* x ps <-> E. y A. x ( ps -> x = y ) ) )

  proof
    wps
    vx
    wmo
    wps
    vx
    vu
    weq
    #
    wi
    #
    vx
    wal
    #
    vu
    wex
    wph
    wps
    vx
    vy
    weq
    #
    wi
    #
    vx
    wal
    #
    vy
    wex
    wps
    vx
    vu
    mo2v
    wph
    @2
    @5
    vu
    vy
    wl-mo2df.2
    wph
    @1
    vy
    vx
    wl-mo2df.1
    wph
    wps
    @0
    vy
    wl-mo2df.4
    wph
    @3
    vx
    wal
    wn
    #
    @0
    vy
    wnf
    #
    wl-mo2df.3
    @7
    vy
    vx
    vy
    vx
    vu
    nfeqf1
    naecoms
    syl
    nfimd
    nfald
    wph
    vu
    vy
    weq
    #
    @2
    @5
    wb
    #
    wph
    @6
    @8
    @9
    wl-mo2df.3
    @6
    @8
    wa
    @1
    @4
    vx
    @6
    @8
    vx
    vx
    vy
    vx
    nfnae
    vx
    vy
    vu
    nfeqf2
    nfan1
    @8
    @1
    @4
    wb
    @6
    @8
    @0
    @3
    wps
    vu
    vy
    vx
    equequ2
    imbi2d
    adantl
    albid
    sylan
    ex
    cbvexd
    syl5bb
end
