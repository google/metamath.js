include "weq.mm"
include "wal.mm"
include "wb.mm"
include "wex.mm"
include "equequ2.mm"
include "bibi2d.mm"
include "albidv.mm"
include "sps.mm"
include "drex1.mm"
include "wn.mm"
include "hbnae.mm"
include "alrimih.mm"
include "wi.mm"
include "ax-5.mm"
include "notbid.mm"
include "dvelim.mm"
include "naecoms.mm"
include "a1i.mm"
include "cbv2h.mm"
include "syl.mm"
include "df-ex.mm"
include "3bitr4g.mm"
include "pm2.61i.mm"

theorem eujustALT
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint ph y
  disjoint ph z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint ph w
  assert |- ( E. y A. x ( ph <-> x = y ) <-> E. z A. x ( ph <-> x = z ) )

  proof
    vy
    vz
    weq
    #
    vy
    wal
    #
    wph
    vx
    vy
    weq
    #
    wb
    #
    vx
    wal
    #
    vy
    wex
    #
    wph
    vx
    vz
    weq
    #
    wb
    #
    vx
    wal
    #
    vz
    wex
    #
    wb
    @4
    @8
    vy
    vz
    @0
    @4
    @8
    wb
    vy
    @0
    @3
    @7
    vx
    @0
    @2
    @6
    wph
    vy
    vz
    vx
    equequ2
    bibi2d
    albidv
    #
    sps
    drex1
    @1
    wn
    #
    @4
    wn
    #
    vy
    wal
    #
    wn
    @8
    wn
    #
    vz
    wal
    #
    wn
    @5
    @9
    @11
    @13
    @15
    @11
    @11
    vz
    wal
    #
    vy
    wal
    @13
    @15
    wb
    @11
    @16
    vy
    vy
    vz
    vy
    hbnae
    vy
    vz
    vz
    hbnae
    alrimih
    @11
    @12
    @14
    vy
    vz
    @12
    @12
    vz
    wal
    wi
    vz
    vy
    wph
    vx
    vw
    weq
    #
    wb
    #
    vx
    wal
    #
    wn
    #
    @12
    vz
    vy
    vw
    @20
    vz
    ax-5
    vw
    vy
    weq
    #
    @19
    @4
    @21
    @18
    @3
    vx
    @21
    @17
    @2
    wph
    vw
    vy
    vx
    equequ2
    bibi2d
    albidv
    notbid
    dvelim
    naecoms
    @20
    @14
    vy
    vz
    vw
    @20
    vy
    ax-5
    vw
    vz
    weq
    #
    @19
    @8
    @22
    @18
    @7
    vx
    @22
    @17
    @6
    wph
    vw
    vz
    vx
    equequ2
    bibi2d
    albidv
    notbid
    dvelim
    @0
    @12
    @14
    wb
    wi
    @11
    @0
    @4
    @8
    @10
    notbid
    a1i
    cbv2h
    syl
    notbid
    @4
    vy
    df-ex
    @8
    vz
    df-ex
    3bitr4g
    pm2.61i
end
