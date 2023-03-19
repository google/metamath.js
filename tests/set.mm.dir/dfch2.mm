include "cch.mm"
include "cv.mm"
include "chil.mm"
include "cpw.mm"
include "wcel.mm"
include "cort.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cab.mm"
include "crab.mm"
include "wss.mm"
include "chss.mm"
include "ococ.mm"
include "jca.mm"
include "occl.mm"
include "3syl.mm"
include "eleq1.mm"
include "syl5ib.mm"
include "impcom.mm"
include "impbii.mm"
include "selpw.mm"
include "anbi1i.mm"
include "bitr4i.mm"
include "abbi2i.mm"
include "df-rab.mm"
include "eqtr4i.mm"

theorem dfch2
  let vx: setvar x


  assert |- CH = { x e. ~P ~H | ( _|_ ` ( _|_ ` x ) ) = x }

  proof
    cch
    vx
    cv
    #
    chil
    cpw
    #
    wcel
    #
    @0
    cort
    cfv
    #
    cort
    cfv
    #
    @0
    wceq
    #
    wa
    #
    vx
    cab
    @5
    vx
    @1
    crab
    @6
    vx
    cch
    @0
    cch
    wcel
    #
    @0
    chil
    wss
    #
    @5
    wa
    #
    @6
    @7
    @9
    @7
    @8
    @5
    @0
    chss
    @0
    ococ
    jca
    @5
    @8
    @7
    @8
    @4
    cch
    wcel
    #
    @5
    @7
    @8
    @3
    cch
    wcel
    @3
    chil
    wss
    @10
    @0
    occl
    @3
    chss
    @3
    occl
    3syl
    @4
    @0
    cch
    eleq1
    syl5ib
    impcom
    impbii
    @2
    @8
    @5
    vx
    chil
    selpw
    anbi1i
    bitr4i
    abbi2i
    @5
    vx
    @1
    df-rab
    eqtr4i
end
