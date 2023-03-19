include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "crnk.mm"
include "cfv.mm"
include "csuc.mm"
include "cpw.mm"
include "wss.mm"
include "wtr.mm"
include "r1tr.mm"
include "rankidb.mm"
include "trss.mm"
include "mpsyl.mm"
include "cdm.mm"
include "wceq.mm"
include "rankdmr1.mm"
include "r1sucg.mm"
include "ax-mp.mm"
include "syl6sseq.mm"
include "sspwuni.mm"
include "sylib.mm"
include "fvex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "syl6eleqr.mm"
include "r1elwf.mm"
include "syl.mm"
include "pwwf.mm"
include "pwuni.mm"
include "sswf.mm"
include "mpan2.mm"
include "sylbi.mm"
include "impbii.mm"

theorem uniwf
  let cA: class A


  assert |- ( A e. U. ( R1 " On ) <-> U. A e. U. ( R1 " On ) )

  proof
    cA
    cr1
    con0
    cima
    cuni
    #
    wcel
    #
    cA
    cuni
    #
    @0
    wcel
    #
    @1
    @2
    cA
    crnk
    cfv
    #
    csuc
    #
    cr1
    cfv
    #
    wcel
    @3
    @1
    @2
    @4
    cr1
    cfv
    #
    cpw
    #
    @6
    @1
    @2
    @7
    wss
    #
    @2
    @8
    wcel
    @1
    cA
    @8
    wss
    @9
    @1
    cA
    @6
    @8
    @6
    wtr
    @1
    cA
    @6
    wcel
    cA
    @6
    wss
    @5
    r1tr
    cA
    rankidb
    @6
    cA
    trss
    mpsyl
    @4
    cr1
    cdm
    wcel
    @6
    @8
    wceq
    cA
    rankdmr1
    @4
    r1sucg
    ax-mp
    #
    syl6sseq
    cA
    @7
    sspwuni
    sylib
    @2
    @7
    @4
    cr1
    fvex
    elpw2
    sylibr
    @10
    syl6eleqr
    @2
    @5
    r1elwf
    syl
    @3
    @2
    cpw
    #
    @0
    wcel
    #
    @1
    @2
    pwwf
    @12
    cA
    @11
    wss
    @1
    cA
    pwuni
    @11
    cA
    sswf
    mpan2
    sylbi
    impbii
end
