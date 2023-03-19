include "cmagm.mm"
include "cexid.mm"
include "cin.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cdm.mm"
include "wa.mm"
include "crn.mm"
include "rngopidOLD.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "pm5.32i.mm"
include "inss1.mm"
include "sseli.mm"
include "eqid.mm"
include "clmgmOLD.mm"
include "syl3an1.mm"
include "3expb.mm"
include "sylbi.mm"
include "3impb.mm"
include "wceq.mm"
include "3ad2ant1.mm"
include "eleqtrrd.mm"

theorem exidcl
  let cA: class A
  let cB: class B
  let cG: class G
  let cX: class X
  assume exidcl.1: |- X = ran G


  assert |- ( ( G e. ( Magma i^i ExId ) /\ A e. X /\ B e. X ) -> ( A G B ) e. X )

  proof
    cG
    cmagm
    cexid
    cin
    #
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    cA
    cB
    cG
    co
    #
    cG
    cdm
    cdm
    #
    cX
    @1
    @2
    @3
    @4
    @5
    wcel
    #
    @1
    @2
    @3
    wa
    #
    wa
    @1
    cA
    @5
    wcel
    #
    cB
    @5
    wcel
    #
    wa
    #
    wa
    @6
    @1
    @7
    @10
    @1
    @2
    @8
    @3
    @9
    @1
    cX
    @5
    cA
    @1
    cX
    cG
    crn
    @5
    exidcl.1
    cG
    rngopidOLD
    syl5eq
    #
    eleq2d
    @1
    cX
    @5
    cB
    @11
    eleq2d
    anbi12d
    pm5.32i
    @1
    @8
    @9
    @6
    @1
    cG
    cmagm
    wcel
    @8
    @9
    @6
    @0
    cmagm
    cG
    cmagm
    cexid
    inss1
    sseli
    cA
    cB
    cG
    @5
    @5
    eqid
    clmgmOLD
    syl3an1
    3expb
    sylbi
    3impb
    @1
    @2
    cX
    @5
    wceq
    @3
    @11
    3ad2ant1
    eleqtrrd
end
