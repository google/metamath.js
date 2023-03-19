include "cv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wal.mm"
include "cxp.mm"
include "cin.mm"
include "wfr.mm"
include "wb.mm"
include "wcel.mm"
include "ssel.mm"
include "anim12d.mm"
include "brinxp.mm"
include "ancoms.mm"
include "syl6.mm"
include "impl.mm"
include "notbid.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "adantr.mm"
include "pm5.74i.mm"
include "albii.mm"
include "df-fr.mm"
include "3bitr4i.mm"

theorem frinxp
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( R Fr A <-> ( R i^i ( A X. A ) ) Fr A )

  proof
    vz
    cv
    #
    cA
    wss
    #
    @0
    c0
    wne
    #
    wa
    #
    vy
    cv
    #
    vx
    cv
    #
    cR
    wbr
    #
    wn
    #
    vy
    @0
    wral
    #
    vx
    @0
    wrex
    #
    wi
    #
    vz
    wal
    @3
    @4
    @5
    cR
    cA
    cA
    cxp
    cin
    #
    wbr
    #
    wn
    #
    vy
    @0
    wral
    #
    vx
    @0
    wrex
    #
    wi
    #
    vz
    wal
    cA
    cR
    wfr
    cA
    @11
    wfr
    @10
    @16
    vz
    @3
    @9
    @15
    @1
    @9
    @15
    wb
    @2
    @1
    @8
    @14
    vx
    @0
    @1
    @5
    @0
    wcel
    #
    wa
    #
    @7
    @13
    vy
    @0
    @18
    @4
    @0
    wcel
    #
    wa
    @6
    @12
    @1
    @17
    @19
    @6
    @12
    wb
    #
    @1
    @17
    @19
    wa
    @5
    cA
    wcel
    #
    @4
    cA
    wcel
    #
    wa
    @20
    @1
    @17
    @21
    @19
    @22
    @0
    cA
    @5
    ssel
    @0
    cA
    @4
    ssel
    anim12d
    @22
    @21
    @20
    @4
    @5
    cA
    cA
    cR
    brinxp
    ancoms
    syl6
    impl
    notbid
    ralbidva
    rexbidva
    adantr
    pm5.74i
    albii
    vz
    vx
    vy
    cA
    cR
    df-fr
    vz
    vx
    vy
    cA
    @11
    df-fr
    3bitr4i
end
