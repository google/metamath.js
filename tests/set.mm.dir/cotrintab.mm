include "cab.mm"
include "cint.mm"
include "ccom.mm"
include "wss.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "cotr.mm"
include "pm3.43.mm"
include "biimpi.mm"
include "2sp.mm"
include "sps.mm"
include "3syl.mm"
include "sylcom.mm"
include "alanimi.mm"
include "cop.mm"
include "wcel.mm"
include "opex.mm"
include "elintab.mm"
include "df-br.mm"
include "imbi2i.mm"
include "albii.mm"
include "3bitr4i.mm"
include "anbi12i.mm"
include "3imtr4i.mm"
include "gen2.mm"
include "mpgbir.mm"

theorem cotrintab
  let wph: wff ph
  let vx: setvar x
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume cotrintab.min: |- ( ph -> ( x o. x ) C_ x )


  assert |- ( |^| { x | ph } o. |^| { x | ph } ) C_ |^| { x | ph }

  proof
    wph
    vx
    cab
    cint
    #
    @0
    ccom
    @0
    wss
    vu
    cv
    #
    vw
    cv
    #
    @0
    wbr
    #
    @2
    vv
    cv
    #
    @0
    wbr
    #
    wa
    #
    @1
    @4
    @0
    wbr
    #
    wi
    #
    vv
    wal
    vw
    wal
    vu
    vu
    vw
    vv
    @0
    cotr
    @8
    vw
    vv
    wph
    @1
    @2
    vx
    cv
    #
    wbr
    #
    wi
    #
    vx
    wal
    #
    wph
    @2
    @4
    @9
    wbr
    #
    wi
    #
    vx
    wal
    #
    wa
    wph
    @1
    @4
    @9
    wbr
    #
    wi
    #
    vx
    wal
    #
    @6
    @7
    @11
    @14
    @17
    vx
    @11
    @14
    wa
    wph
    @10
    @13
    wa
    #
    @16
    wph
    @10
    @13
    pm3.43
    wph
    @9
    @9
    ccom
    @9
    wss
    #
    @19
    @16
    wi
    #
    vv
    wal
    vw
    wal
    #
    vu
    wal
    #
    @21
    cotrintab.min
    @20
    @23
    vu
    vw
    vv
    @9
    cotr
    biimpi
    @22
    @21
    vu
    @21
    vw
    vv
    2sp
    sps
    3syl
    sylcom
    alanimi
    @3
    @12
    @5
    @15
    @1
    @2
    cop
    #
    @0
    wcel
    wph
    @24
    @9
    wcel
    #
    wi
    #
    vx
    wal
    @3
    @12
    wph
    vx
    @24
    @1
    @2
    opex
    elintab
    @1
    @2
    @0
    df-br
    @11
    @26
    vx
    @10
    @25
    wph
    @1
    @2
    @9
    df-br
    imbi2i
    albii
    3bitr4i
    @2
    @4
    cop
    #
    @0
    wcel
    wph
    @27
    @9
    wcel
    #
    wi
    #
    vx
    wal
    @5
    @15
    wph
    vx
    @27
    @2
    @4
    opex
    elintab
    @2
    @4
    @0
    df-br
    @14
    @29
    vx
    @13
    @28
    wph
    @2
    @4
    @9
    df-br
    imbi2i
    albii
    3bitr4i
    anbi12i
    @1
    @4
    cop
    #
    @0
    wcel
    wph
    @30
    @9
    wcel
    #
    wi
    #
    vx
    wal
    @7
    @18
    wph
    vx
    @30
    @1
    @4
    opex
    elintab
    @1
    @4
    @0
    df-br
    @17
    @32
    vx
    @16
    @31
    wph
    @1
    @4
    @9
    df-br
    imbi2i
    albii
    3bitr4i
    3imtr4i
    gen2
    mpgbir
end
