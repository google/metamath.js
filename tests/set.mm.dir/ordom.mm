include "com.mm"
include "wtr.mm"
include "con0.mm"
include "wss.mm"
include "word.mm"
include "wel.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "dftr2.mm"
include "wlim.mm"
include "onelon.mm"
include "expcom.mm"
include "limord.mm"
include "ordtr.mm"
include "trel.mm"
include "3syl.mm"
include "expd.mm"
include "com12.mm"
include "a2d.mm"
include "alimdv.mm"
include "anim12d.mm"
include "elom.mm"
include "3imtr4g.mm"
include "imp.mm"
include "ax-gen.mm"
include "mpgbir.mm"
include "omsson.mm"
include "ordon.mm"
include "trssord.mm"
include "mp3an.mm"

theorem ordom
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- Ord _om

  proof
    com
    wtr
    #
    com
    con0
    wss
    con0
    word
    com
    word
    @0
    vy
    vx
    wel
    #
    vx
    cv
    #
    com
    wcel
    #
    wa
    vy
    cv
    #
    com
    wcel
    #
    wi
    #
    vx
    wal
    vy
    vy
    vx
    com
    dftr2
    @6
    vx
    @1
    @3
    @5
    @1
    @2
    con0
    wcel
    #
    vz
    cv
    #
    wlim
    #
    vx
    vz
    wel
    #
    wi
    #
    vz
    wal
    #
    wa
    @4
    con0
    wcel
    #
    @9
    vy
    vz
    wel
    #
    wi
    #
    vz
    wal
    #
    wa
    @3
    @5
    @1
    @7
    @13
    @12
    @16
    @7
    @1
    @13
    @2
    @4
    onelon
    expcom
    @1
    @11
    @15
    vz
    @1
    @9
    @10
    @14
    @9
    @1
    @10
    @14
    wi
    @9
    @1
    @10
    @14
    @9
    @8
    word
    @8
    wtr
    @1
    @10
    wa
    @14
    wi
    @8
    limord
    @8
    ordtr
    @8
    @4
    @2
    trel
    3syl
    expd
    com12
    a2d
    alimdv
    anim12d
    vz
    @2
    elom
    vz
    @4
    elom
    3imtr4g
    imp
    ax-gen
    mpgbir
    omsson
    ordon
    com
    con0
    trssord
    mp3an
end
