include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "wne.mm"
include "w3a.mm"
include "cpr.mm"
include "wi.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "hash2prb.mm"
include "simpr.mm"
include "3simpa.mm"
include "adantl.mm"
include "adantr.mm"
include "wb.mm"
include "eleq2.mm"
include "anbi12d.mm"
include "mpbid.mm"
include "wn.mm"
include "simpl.mm"
include "anim12ci.mm"
include "neneq.mm"
include "3ad2ant3.mm"
include "prel12g.mm"
include "sylc.mm"
include "mpbird.mm"
include "eqtr4d.mm"
include "exp31.mm"
include "com23.mm"
include "expimpd.mm"
include "rexlimivv.mm"
include "syl6bi.mm"
include "imp.mm"

theorem hash2prd
  let cP: class P
  let cV: class V
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( P e. V /\ ( # ` P ) = 2 ) -> ( ( X e. P /\ Y e. P /\ X =/= Y ) -> P = { X , Y } ) )

  proof
    cP
    cV
    wcel
    #
    cP
    chash
    cfv
    c2
    wceq
    #
    cX
    cP
    wcel
    #
    cY
    cP
    wcel
    #
    cX
    cY
    wne
    #
    w3a
    #
    cP
    cX
    cY
    cpr
    #
    wceq
    #
    wi
    #
    @0
    @1
    vx
    cv
    #
    vy
    cv
    #
    wne
    #
    cP
    @9
    @10
    cpr
    #
    wceq
    #
    wa
    #
    vy
    cP
    wrex
    vx
    cP
    wrex
    @8
    cP
    cV
    vx
    vy
    hash2prb
    @14
    @8
    vx
    vy
    cP
    cP
    @9
    cP
    wcel
    @10
    cP
    wcel
    wa
    #
    @11
    @13
    @8
    @15
    @11
    wa
    #
    @5
    @13
    @7
    @16
    @5
    @13
    @7
    @16
    @5
    wa
    #
    @13
    wa
    #
    cP
    @12
    @6
    @17
    @13
    simpr
    @18
    @6
    @12
    wceq
    #
    cX
    @12
    wcel
    #
    cY
    @12
    wcel
    #
    wa
    #
    @18
    @2
    @3
    wa
    #
    @22
    @17
    @23
    @13
    @5
    @23
    @16
    @2
    @3
    @4
    3simpa
    #
    adantl
    adantr
    @13
    @23
    @22
    wb
    @17
    @13
    @2
    @20
    @3
    @21
    cP
    @12
    cX
    eleq2
    cP
    @12
    cY
    eleq2
    anbi12d
    adantl
    mpbid
    @17
    @19
    @22
    wb
    #
    @13
    @17
    @23
    @15
    wa
    cX
    cY
    wceq
    wn
    #
    @25
    @16
    @15
    @5
    @23
    @15
    @11
    simpl
    @24
    anim12ci
    @5
    @26
    @16
    @4
    @2
    @26
    @3
    cX
    cY
    neneq
    3ad2ant3
    adantl
    cX
    cY
    @9
    @10
    cP
    cP
    cP
    cP
    prel12g
    sylc
    adantr
    mpbird
    eqtr4d
    exp31
    com23
    expimpd
    rexlimivv
    syl6bi
    imp
end
