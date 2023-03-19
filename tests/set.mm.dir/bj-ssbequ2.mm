include "wssb.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "df-ssb.mm"
include "wa.mm"
include "sp.mm"
include "imim2i.mm"
include "alimi.mm"
include "pm3.31.mm"
include "wex.mm"
include "19.23v.mm"
include "equviniva.mm"
include "biid.mm"
include "equcom.mm"
include "anbi12ci.mm"
include "biimpi.mm"
include "eximi.mm"
include "pm3.35.mm"
include "sylan.mm"
include "ancoms.mm"
include "sylan2.mm"
include "ex.mm"
include "sylbi.mm"
include "3syl.mm"
include "com12.mm"

theorem bj-ssbequ2
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let vy: setvar y


  assert |- ( x = t -> ( [b t /b x ]b ph -> ph ) )

  proof
    wph
    vx
    vt
    wssb
    #
    vx
    vt
    weq
    #
    wph
    @0
    vy
    vt
    weq
    #
    vx
    vy
    weq
    #
    wph
    wi
    #
    vx
    wal
    #
    wi
    #
    vy
    wal
    #
    @1
    wph
    wi
    #
    wph
    vx
    vy
    vt
    df-ssb
    @7
    @2
    @4
    wi
    #
    vy
    wal
    @2
    @3
    wa
    #
    wph
    wi
    #
    vy
    wal
    #
    @8
    @6
    @9
    vy
    @5
    @4
    @2
    @4
    vx
    sp
    imim2i
    alimi
    @9
    @11
    vy
    @2
    @3
    wph
    pm3.31
    alimi
    @12
    @10
    vy
    wex
    #
    wph
    wi
    #
    @8
    @10
    wph
    vy
    19.23v
    @14
    @1
    wph
    @1
    @14
    @3
    vt
    vy
    weq
    #
    wa
    #
    vy
    wex
    #
    wph
    vx
    vt
    vy
    equviniva
    @17
    @14
    wph
    @17
    @13
    @14
    wph
    @16
    @10
    vy
    @16
    @10
    @3
    @3
    @15
    @2
    @3
    biid
    vt
    vy
    equcom
    anbi12ci
    biimpi
    eximi
    @13
    wph
    pm3.35
    sylan
    ancoms
    sylan2
    ex
    sylbi
    3syl
    sylbi
    com12
end
