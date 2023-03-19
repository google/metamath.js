include "weu.mm"
include "wi.mm"
include "wal.mm"
include "cio.mm"
include "wsbc.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wex.mm"
include "df-eu.mm"
include "biimpi.mm"
include "iota4.mm"
include "iotaval.mm"
include "eqcomd.mm"
include "wsb.mm"
include "spsbim.mm"
include "sbsbc.mm"
include "3imtr3g.mm"
include "dfsbcq.mm"
include "imbi12d.mm"
include "syl5ib.mm"
include "com23.mm"
include "syl.mm"
include "exlimiv.mm"
include "sylc.mm"
include "wa.mm"
include "cvv.mm"
include "wcel.mm"
include "iotaexeu.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "sbcan.mm"
include "spesbc.mm"
include "sylbir.mm"
include "vtoclg.mm"
include "expd.mm"
include "anc2li.mm"
include "eupicka.mm"
include "syl6.mm"
include "impbid.mm"

theorem sbiota1
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( E! x ph -> ( A. x ( ph -> ps ) <-> [. ( iota x ph ) / x ]. ps ) )

  proof
    wph
    vx
    weu
    #
    wph
    wps
    wi
    vx
    wal
    #
    wps
    vx
    wph
    vx
    cio
    #
    wsbc
    #
    @0
    wph
    vx
    cv
    vy
    cv
    #
    wceq
    wb
    vx
    wal
    #
    vy
    wex
    #
    wph
    vx
    @2
    wsbc
    #
    @1
    @3
    wi
    #
    @0
    @6
    wph
    vx
    vy
    df-eu
    biimpi
    wph
    vx
    iota4
    #
    @5
    @7
    @8
    wi
    #
    vy
    @5
    @4
    @2
    wceq
    #
    @10
    @5
    @2
    @4
    wph
    vx
    vy
    iotaval
    eqcomd
    @11
    @1
    @7
    @3
    @1
    wph
    vx
    @4
    wsbc
    #
    wps
    vx
    @4
    wsbc
    #
    wi
    @11
    @7
    @3
    wi
    @1
    wph
    vx
    vy
    wsb
    wps
    vx
    vy
    wsb
    @12
    @13
    wph
    wps
    vx
    vy
    spsbim
    wph
    vx
    vy
    sbsbc
    wps
    vx
    vy
    sbsbc
    3imtr3g
    @11
    @12
    @7
    @13
    @3
    wph
    vx
    @4
    @2
    dfsbcq
    #
    wps
    vx
    @4
    @2
    dfsbcq
    #
    imbi12d
    syl5ib
    com23
    syl
    exlimiv
    sylc
    @0
    @3
    @0
    wph
    wps
    wa
    #
    vx
    wex
    #
    wa
    @1
    @0
    @3
    @17
    @0
    @2
    cvv
    wcel
    #
    @7
    @3
    @17
    wi
    wph
    vx
    iotaexeu
    @9
    @18
    @7
    @3
    @17
    @12
    @13
    wa
    #
    @17
    wi
    @7
    @3
    wa
    #
    @17
    wi
    vy
    @2
    cvv
    @11
    @19
    @20
    @17
    @11
    @12
    @7
    @13
    @3
    @14
    @15
    anbi12d
    imbi1d
    @19
    @16
    vx
    @4
    wsbc
    @17
    wph
    wps
    vx
    @4
    sbcan
    @16
    vx
    @4
    spesbc
    sylbir
    vtoclg
    expd
    sylc
    anc2li
    wph
    wps
    vx
    eupicka
    syl6
    impbid
end
