include "weq.mm"
include "wex.mm"
include "wsb.mm"
include "wb.mm"
include "wi.mm"
include "ax6ev.mm"
include "wa.mm"
include "wal.mm"
include "wn.mm"
include "wl-sbcom2d-lem2.mm"
include "alcom.mm"
include "ancomst.mm"
include "2albii.mm"
include "bitri.mm"
include "syl6bb.mm"
include "naecoms.mm"
include "bitr4d.mm"
include "syl.mm"
include "adantl.mm"
include "wl-sbcom2d-lem1.mm"
include "syl5.mm"
include "imp.mm"
include "ancoms.mm"
include "3bitr3rd.mm"
include "exp31.mm"
include "exlimdv.mm"
include "exlimiv.mm"
include "mp2.mm"

theorem wl-sbcom2d
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vu: setvar u
  let vv: setvar v
  assume wl-sbcom2d.1: |- ( ph -> -. A. x x = w )
  assume wl-sbcom2d.2: |- ( ph -> -. A. x x = z )
  assume wl-sbcom2d.3: |- ( ph -> -. A. z z = y )


  assert |- ( ph -> ( [ w / z ] [ y / x ] ps <-> [ y / x ] [ w / z ] ps ) )

  proof
    vu
    vy
    weq
    #
    vu
    wex
    vv
    vw
    weq
    #
    vv
    wex
    #
    wph
    wps
    vx
    vy
    wsb
    vz
    vw
    wsb
    #
    wps
    vz
    vw
    wsb
    vx
    vy
    wsb
    #
    wb
    #
    wi
    #
    vu
    vy
    ax6ev
    vv
    vw
    ax6ev
    @0
    @2
    @6
    wi
    vu
    @0
    @1
    @6
    vv
    @0
    @1
    wph
    @5
    @0
    @1
    wa
    #
    wph
    wa
    wps
    vz
    vv
    wsb
    vx
    vu
    wsb
    #
    wps
    vx
    vu
    wsb
    vz
    vv
    wsb
    #
    @4
    @3
    wph
    @8
    @9
    wb
    #
    @7
    wph
    vx
    vz
    weq
    vx
    wal
    wn
    #
    @10
    wl-sbcom2d.2
    @11
    @8
    vz
    vv
    weq
    #
    vx
    vu
    weq
    #
    wa
    wps
    wi
    #
    vx
    wal
    vz
    wal
    #
    @9
    @8
    @15
    wb
    vz
    vx
    vz
    vx
    weq
    vz
    wal
    wn
    @8
    @13
    @12
    wa
    wps
    wi
    #
    vz
    wal
    vx
    wal
    #
    @15
    wps
    vx
    vz
    vv
    vu
    wl-sbcom2d-lem2
    @17
    @16
    vx
    wal
    vz
    wal
    @15
    @16
    vx
    vz
    alcom
    @16
    @14
    vz
    vx
    @13
    @12
    wps
    ancomst
    2albii
    bitri
    syl6bb
    naecoms
    wps
    vz
    vx
    vu
    vv
    wl-sbcom2d-lem2
    bitr4d
    syl
    adantl
    @7
    wph
    @8
    @4
    wb
    #
    wph
    vx
    vw
    weq
    vx
    wal
    wn
    @7
    @18
    wl-sbcom2d.1
    wps
    vx
    vy
    vz
    vw
    vv
    vu
    wl-sbcom2d-lem1
    syl5
    imp
    @7
    wph
    @9
    @3
    wb
    #
    @1
    @0
    wph
    @19
    wi
    wph
    vz
    vy
    weq
    vz
    wal
    wn
    @1
    @0
    wa
    @19
    wl-sbcom2d.3
    wps
    vz
    vw
    vx
    vy
    vu
    vv
    wl-sbcom2d-lem1
    syl5
    ancoms
    imp
    3bitr3rd
    exp31
    exlimdv
    exlimiv
    mp2
end
