include "wcel.mm"
include "wfun.mm"
include "cima.mm"
include "cres.mm"
include "cdm.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "crn.mm"
include "df-ima.mm"
include "cvv.mm"
include "wfo.mm"
include "resfunexg.mm"
include "dmexg.mm"
include "syl.mm"
include "funres.mm"
include "funforn.mm"
include "sylib.mm"
include "adantr.mm"
include "fodomg.mm"
include "sylc.mm"
include "syl5eqbr.mm"
include "expcom.mm"
include "wss.mm"
include "cin.mm"
include "dmres.mm"
include "inss1.mm"
include "eqsstri.mm"
include "ssdomg.mm"
include "mpi.mm"
include "domtr.mm"
include "sylan2.mm"
include "syld.mm"

theorem imadomg
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( A e. B -> ( Fun F -> ( F " A ) ~<_ A ) )

  proof
    cA
    cB
    wcel
    #
    cF
    wfun
    #
    cF
    cA
    cima
    #
    cF
    cA
    cres
    #
    cdm
    #
    cdom
    wbr
    #
    @2
    cA
    cdom
    wbr
    #
    @1
    @0
    @5
    @1
    @0
    wa
    #
    @2
    @3
    crn
    #
    @4
    cdom
    cF
    cA
    df-ima
    @7
    @4
    cvv
    wcel
    #
    @4
    @8
    @3
    wfo
    #
    @8
    @4
    cdom
    wbr
    @7
    @3
    cvv
    wcel
    @9
    cF
    cA
    cB
    resfunexg
    @3
    cvv
    dmexg
    syl
    @1
    @10
    @0
    @1
    @3
    wfun
    @10
    cA
    cF
    funres
    @3
    funforn
    sylib
    adantr
    @4
    @8
    cvv
    @3
    fodomg
    sylc
    syl5eqbr
    expcom
    @5
    @0
    @6
    @0
    @5
    @4
    cA
    cdom
    wbr
    #
    @6
    @0
    @4
    cA
    wss
    @11
    @4
    cA
    cF
    cdm
    #
    cin
    cA
    cF
    cA
    dmres
    cA
    @12
    inss1
    eqsstri
    @4
    cA
    cB
    ssdomg
    mpi
    @2
    @4
    cA
    domtr
    sylan2
    expcom
    syld
end
