include "wwe.mm"
include "wse.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "wor.mm"
include "weso.mm"
include "3ad2ant1.mm"
include "cv.mm"
include "cpred.mm"
include "wceq.mm"
include "wrex.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "wss.mm"
include "simp1.mm"
include "simp2.mm"
include "ssid.mm"
include "a1i.mm"
include "simp3.mm"
include "tz6.26.mm"
include "syl22anc.mm"
include "wcel.mm"
include "wal.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "elpred.mm"
include "ax-mp.mm"
include "notbii.mm"
include "imnan.mm"
include "bitr4i.mm"
include "pm2.27.mm"
include "ad2antll.mm"
include "breq1.mm"
include "rspcev.mm"
include "ex.mm"
include "ad2antrl.mm"
include "jctird.mm"
include "syl5bi.mm"
include "expr.mm"
include "com23.mm"
include "alimdv.mm"
include "eq0.mm"
include "r19.26.mm"
include "df-ral.mm"
include "bitr3i.mm"
include "3imtr4g.mm"
include "reximdva.mm"
include "mpd.mm"
include "infcl.mm"

theorem wzel
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( R We A /\ R Se A /\ A =/= (/) ) -> inf ( A , A , R ) e. A )

  proof
    cA
    cR
    wwe
    #
    cA
    cR
    wse
    #
    cA
    c0
    wne
    #
    w3a
    #
    vx
    vy
    vz
    cA
    cA
    cR
    @0
    @1
    cA
    cR
    wor
    @2
    cA
    cR
    weso
    3ad2ant1
    @3
    cA
    cR
    vx
    cv
    #
    cpred
    #
    c0
    wceq
    #
    vx
    cA
    wrex
    #
    vy
    cv
    #
    @4
    cR
    wbr
    #
    wn
    #
    vy
    cA
    wral
    @4
    @8
    cR
    wbr
    #
    vz
    cv
    #
    @8
    cR
    wbr
    #
    vz
    cA
    wrex
    #
    wi
    #
    vy
    cA
    wral
    wa
    #
    vx
    cA
    wrex
    @3
    @0
    @1
    cA
    cA
    wss
    #
    @2
    @7
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    @17
    @3
    cA
    ssid
    a1i
    @0
    @1
    @2
    simp3
    vx
    cA
    cA
    cR
    tz6.26
    syl22anc
    @3
    @6
    @16
    vx
    cA
    @3
    @4
    cA
    wcel
    #
    wa
    #
    @8
    @5
    wcel
    #
    wn
    #
    vy
    wal
    @8
    cA
    wcel
    #
    @10
    @15
    wa
    #
    wi
    #
    vy
    wal
    #
    @6
    @16
    @19
    @21
    @24
    vy
    @19
    @22
    @21
    @23
    @3
    @18
    @22
    @21
    @23
    wi
    @21
    @22
    @10
    wi
    #
    @3
    @18
    @22
    wa
    wa
    #
    @23
    @21
    @22
    @9
    wa
    #
    wn
    @26
    @20
    @28
    @4
    cvv
    wcel
    @20
    @28
    wb
    vx
    vex
    cA
    cvv
    cR
    @4
    @8
    vy
    vex
    elpred
    ax-mp
    notbii
    @22
    @9
    imnan
    bitr4i
    @27
    @26
    @10
    @15
    @22
    @26
    @10
    wi
    @3
    @18
    @22
    @10
    pm2.27
    ad2antll
    @18
    @15
    @3
    @22
    @18
    @11
    @14
    @13
    @11
    vz
    @4
    cA
    @12
    @4
    @8
    cR
    breq1
    rspcev
    ex
    ad2antrl
    jctird
    syl5bi
    expr
    com23
    alimdv
    vy
    @5
    eq0
    @16
    @23
    vy
    cA
    wral
    @25
    @10
    @15
    vy
    cA
    r19.26
    @23
    vy
    cA
    df-ral
    bitr3i
    3imtr4g
    reximdva
    mpd
    infcl
end
