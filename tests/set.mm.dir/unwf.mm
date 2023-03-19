include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "wa.mm"
include "cun.mm"
include "crnk.mm"
include "cfv.mm"
include "csuc.mm"
include "cpw.mm"
include "wss.mm"
include "r1rankidb.mm"
include "adantr.mm"
include "ssun1.mm"
include "cdm.mm"
include "wi.mm"
include "rankdmr1.mm"
include "word.mm"
include "wlim.mm"
include "wfun.mm"
include "r1funlim.mm"
include "simpri.mm"
include "limord.mm"
include "ax-mp.mm"
include "ordunel.mm"
include "mp3an.mm"
include "r1ord3g.mm"
include "mp2an.mm"
include "syl6ss.mm"
include "adantl.mm"
include "ssun2.mm"
include "unssd.mm"
include "fvex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "wceq.mm"
include "r1sucg.mm"
include "syl6eleqr.mm"
include "r1elwf.mm"
include "syl.mm"
include "sswf.mm"
include "mpan2.mm"
include "jca.mm"
include "impbii.mm"

theorem unwf
  let cA: class A
  let cB: class B


  assert |- ( ( A e. U. ( R1 " On ) /\ B e. U. ( R1 " On ) ) <-> ( A u. B ) e. U. ( R1 " On ) )

  proof
    cA
    cr1
    con0
    cima
    cuni
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    cA
    cB
    cun
    #
    @0
    wcel
    #
    @3
    @4
    cA
    crnk
    cfv
    #
    cB
    crnk
    cfv
    #
    cun
    #
    csuc
    #
    cr1
    cfv
    #
    wcel
    @5
    @3
    @4
    @8
    cr1
    cfv
    #
    cpw
    #
    @10
    @3
    @4
    @11
    wss
    @4
    @12
    wcel
    @3
    cA
    cB
    @11
    @3
    cA
    @6
    cr1
    cfv
    #
    @11
    @1
    cA
    @13
    wss
    @2
    cA
    r1rankidb
    adantr
    @6
    @8
    wss
    #
    @13
    @11
    wss
    #
    @6
    @7
    ssun1
    @6
    cr1
    cdm
    #
    wcel
    #
    @8
    @16
    wcel
    #
    @14
    @15
    wi
    cA
    rankdmr1
    #
    @16
    word
    #
    @17
    @7
    @16
    wcel
    #
    @18
    @16
    wlim
    #
    @20
    cr1
    wfun
    @22
    r1funlim
    simpri
    @16
    limord
    ax-mp
    @19
    cB
    rankdmr1
    #
    @16
    @6
    @7
    ordunel
    mp3an
    #
    @6
    @8
    r1ord3g
    mp2an
    ax-mp
    syl6ss
    @3
    cB
    @7
    cr1
    cfv
    #
    @11
    @2
    cB
    @25
    wss
    @1
    cB
    r1rankidb
    adantl
    @7
    @8
    wss
    #
    @25
    @11
    wss
    #
    @7
    @6
    ssun2
    @21
    @18
    @26
    @27
    wi
    @23
    @24
    @7
    @8
    r1ord3g
    mp2an
    ax-mp
    syl6ss
    unssd
    @4
    @11
    @8
    cr1
    fvex
    elpw2
    sylibr
    @18
    @10
    @12
    wceq
    @24
    @8
    r1sucg
    ax-mp
    syl6eleqr
    @4
    @9
    r1elwf
    syl
    @5
    @1
    @2
    @5
    cA
    @4
    wss
    @1
    cA
    cB
    ssun1
    @4
    cA
    sswf
    mpan2
    @5
    cB
    @4
    wss
    @2
    cB
    cA
    ssun2
    @4
    cB
    sswf
    mpan2
    jca
    impbii
end
