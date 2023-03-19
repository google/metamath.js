include "cio.mm"
include "wsbc.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "weu.mm"
include "wb.mm"
include "wal.mm"
include "sbc5.mm"
include "wi.mm"
include "cvv.mm"
include "wcel.mm"
include "iotaexeu.mm"
include "eueq.mm"
include "sylib.mm"
include "df-eu.mm"
include "iotaval.mm"
include "eqcomd.mm"
include "ancri.mm"
include "eximi.mm"
include "sylbi.mm"
include "eupick.mm"
include "syl2anc.mm"
include "impbid1.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "syl5bb.mm"

theorem iotasbc
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  disjoint ph y
  assert |- ( E! x ph -> ( [. ( iota x ph ) / y ]. ps <-> E. y ( A. x ( ph <-> x = y ) /\ ps ) ) )

  proof
    wps
    vy
    wph
    vx
    cio
    #
    wsbc
    vy
    cv
    #
    @0
    wceq
    #
    wps
    wa
    #
    vy
    wex
    wph
    vx
    weu
    #
    wph
    vx
    cv
    @1
    wceq
    wb
    vx
    wal
    #
    wps
    wa
    #
    vy
    wex
    wps
    vy
    @0
    sbc5
    @4
    @3
    @6
    vy
    @4
    @2
    @5
    wps
    @4
    @2
    @5
    @4
    @2
    vy
    weu
    #
    @2
    @5
    wa
    #
    vy
    wex
    #
    @2
    @5
    wi
    @4
    @0
    cvv
    wcel
    @7
    wph
    vx
    iotaexeu
    vy
    @0
    eueq
    sylib
    @4
    @5
    vy
    wex
    @9
    wph
    vx
    vy
    df-eu
    @5
    @8
    vy
    @5
    @2
    @5
    @0
    @1
    wph
    vx
    vy
    iotaval
    eqcomd
    #
    ancri
    eximi
    sylbi
    @2
    @5
    vy
    eupick
    syl2anc
    @10
    impbid1
    anbi1d
    exbidv
    syl5bb
end
