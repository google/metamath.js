include "weu.mm"
include "weq.mm"
include "wb.mm"
include "wal.mm"
include "wex.mm"
include "cio.mm"
include "c0.mm"
include "wceq.mm"
include "df-eu.mm"
include "wn.mm"
include "cab.mm"
include "cuni.mm"
include "dfiota2.mm"
include "alnex.mm"
include "dfnul2.mm"
include "equid.mm"
include "tbt.mm"
include "biimpi.mm"
include "con1bid.mm"
include "alimi.mm"
include "abbi.mm"
include "sylib.mm"
include "syl5req.mm"
include "sylbir.mm"
include "unieqd.mm"
include "uni0.mm"
include "syl6eq.mm"
include "syl5eq.mm"
include "sylnbi.mm"

theorem iotanul
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let wps: wff ps
  let vy: setvar y


  assert |- ( -. E! x ph -> ( iota x ph ) = (/) )

  proof
    wph
    vx
    weu
    wph
    vx
    vz
    weq
    wb
    vx
    wal
    #
    vz
    wex
    #
    wph
    vx
    cio
    #
    c0
    wceq
    wph
    vx
    vz
    df-eu
    @1
    wn
    #
    @2
    @0
    vz
    cab
    #
    cuni
    #
    c0
    wph
    vx
    vz
    dfiota2
    @3
    @5
    c0
    cuni
    c0
    @3
    @4
    c0
    @3
    @0
    wn
    #
    vz
    wal
    #
    @4
    c0
    wceq
    @0
    vz
    alnex
    @7
    c0
    vz
    vz
    weq
    #
    wn
    #
    vz
    cab
    #
    @4
    vz
    dfnul2
    @7
    @9
    @0
    wb
    #
    vz
    wal
    @10
    @4
    wceq
    @6
    @11
    vz
    @6
    @0
    @8
    @6
    @6
    @8
    wb
    @8
    @6
    vz
    equid
    tbt
    biimpi
    con1bid
    alimi
    @9
    @0
    vz
    abbi
    sylib
    syl5req
    sylbir
    unieqd
    uni0
    syl6eq
    syl5eq
    sylnbi
end
