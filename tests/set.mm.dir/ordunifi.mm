include "con0.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cuni.mm"
include "cv.mm"
include "wrex.mm"
include "cep.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wor.mm"
include "wwe.mm"
include "epweon.mm"
include "weso.mm"
include "ax-mp.mm"
include "soss.mm"
include "mpi.mm"
include "fimax2g.mm"
include "syl3an1.mm"
include "wb.mm"
include "wa.mm"
include "ssel2.mm"
include "adantlr.mm"
include "adantr.mm"
include "ontri1.mm"
include "epel.mm"
include "notbii.mm"
include "syl6rbbr.mm"
include "syl2anc.mm"
include "ralbidva.mm"
include "unissb.mm"
include "syl6bbr.mm"
include "rexbidva.mm"
include "3ad2ant1.mm"
include "mpbid.mm"
include "elssuni.mm"
include "wceq.mm"
include "eqss.mm"
include "eleq1.mm"
include "biimpcd.mm"
include "syl5bir.mm"
include "mpand.mm"
include "rexlimiv.mm"
include "syl.mm"

theorem ordunifi
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A C_ On /\ A e. Fin /\ A =/= (/) ) -> U. A e. A )

  proof
    cA
    con0
    wss
    #
    cA
    cfn
    wcel
    #
    cA
    c0
    wne
    #
    w3a
    #
    cA
    cuni
    #
    vx
    cv
    #
    wss
    #
    vx
    cA
    wrex
    #
    @4
    cA
    wcel
    #
    @3
    @5
    vy
    cv
    #
    cep
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    vx
    cA
    wrex
    #
    @7
    @0
    cA
    cep
    wor
    #
    @1
    @2
    @13
    @0
    con0
    cep
    wor
    #
    @14
    con0
    cep
    wwe
    @15
    epweon
    con0
    cep
    weso
    ax-mp
    cA
    con0
    cep
    soss
    mpi
    vx
    vy
    cA
    cep
    fimax2g
    syl3an1
    @0
    @1
    @13
    @7
    wb
    @2
    @0
    @12
    @6
    vx
    cA
    @0
    @5
    cA
    wcel
    #
    wa
    #
    @12
    @9
    @5
    wss
    #
    vy
    cA
    wral
    @6
    @17
    @11
    @18
    vy
    cA
    @17
    @9
    cA
    wcel
    #
    wa
    @9
    con0
    wcel
    #
    @5
    con0
    wcel
    #
    @11
    @18
    wb
    @0
    @19
    @20
    @16
    cA
    con0
    @9
    ssel2
    adantlr
    @17
    @21
    @19
    cA
    con0
    @5
    ssel2
    adantr
    @20
    @21
    wa
    @18
    @5
    @9
    wcel
    #
    wn
    @11
    @9
    @5
    ontri1
    @10
    @22
    vx
    vy
    epel
    notbii
    syl6rbbr
    syl2anc
    ralbidva
    vy
    cA
    @5
    unissb
    syl6bbr
    rexbidva
    3ad2ant1
    mpbid
    @6
    @8
    vx
    cA
    @16
    @5
    @4
    wss
    #
    @6
    @8
    @5
    cA
    elssuni
    @23
    @6
    wa
    @5
    @4
    wceq
    #
    @16
    @8
    @5
    @4
    eqss
    @24
    @16
    @8
    @5
    @4
    cA
    eleq1
    biimpcd
    syl5bir
    mpand
    rexlimiv
    syl
end
