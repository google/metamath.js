include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "crnk.mm"
include "cfv.mm"
include "fveq2.mm"
include "cdm.mm"
include "com.mm"
include "wlim.mm"
include "wss.mm"
include "wfun.mm"
include "r1funlim.mm"
include "simpri.mm"
include "limomss.mm"
include "ax-mp.mm"
include "peano1.mm"
include "sselii.mm"
include "rankonid.mm"
include "mpbi.mm"
include "syl6eq.mm"
include "wa.mm"
include "eqimss.mm"
include "adantl.mm"
include "wb.mm"
include "simpl.mm"
include "rankr1bg.mm"
include "sylancl.mm"
include "mpbird.mm"
include "r10.mm"
include "syl6sseq.mm"
include "ss0.mm"
include "syl.mm"
include "ex.mm"
include "impbid2.mm"

theorem rankeq0b
  let cA: class A


  assert |- ( A e. U. ( R1 " On ) -> ( A = (/) <-> ( rank ` A ) = (/) ) )

  proof
    cA
    cr1
    con0
    cima
    cuni
    wcel
    #
    cA
    c0
    wceq
    #
    cA
    crnk
    cfv
    #
    c0
    wceq
    #
    @1
    @2
    c0
    crnk
    cfv
    #
    c0
    cA
    c0
    crnk
    fveq2
    c0
    cr1
    cdm
    #
    wcel
    #
    @4
    c0
    wceq
    com
    @5
    c0
    @5
    wlim
    #
    com
    @5
    wss
    cr1
    wfun
    @7
    r1funlim
    simpri
    @5
    limomss
    ax-mp
    peano1
    sselii
    #
    c0
    rankonid
    mpbi
    syl6eq
    @0
    @3
    @1
    @0
    @3
    wa
    #
    cA
    c0
    wss
    @1
    @9
    cA
    c0
    cr1
    cfv
    #
    c0
    @9
    cA
    @10
    wss
    #
    @2
    c0
    wss
    #
    @3
    @12
    @0
    @2
    c0
    eqimss
    adantl
    @9
    @0
    @6
    @11
    @12
    wb
    @0
    @3
    simpl
    @8
    cA
    c0
    rankr1bg
    sylancl
    mpbird
    r10
    syl6sseq
    cA
    ss0
    syl
    ex
    impbid2
end
