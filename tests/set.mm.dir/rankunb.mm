include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "wa.mm"
include "cun.mm"
include "crnk.mm"
include "cfv.mm"
include "cv.mm"
include "wral.mm"
include "wi.mm"
include "crab.mm"
include "cint.mm"
include "wceq.mm"
include "unwf.mm"
include "rankval3b.mm"
include "sylbi.mm"
include "eleq2d.mm"
include "vex.mm"
include "elintrab.mm"
include "syl6bb.mm"
include "wo.mm"
include "elun.mm"
include "rankelb.mm"
include "elun1.mm"
include "syl6.mm"
include "elun2.mm"
include "jaao.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "rankon.mm"
include "onun2i.mm"
include "eleq2.mm"
include "ralbidv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "ax-mp.mm"
include "syl5com.mm"
include "sylbid.mm"
include "ssrdv.mm"
include "wss.mm"
include "ssun1.mm"
include "rankssb.mm"
include "mpi.mm"
include "ssun2.mm"
include "unssd.mm"
include "eqssd.mm"

theorem rankunb
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. U. ( R1 " On ) /\ B e. U. ( R1 " On ) ) -> ( rank ` ( A u. B ) ) = ( ( rank ` A ) u. ( rank ` B ) ) )

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
    crnk
    cfv
    #
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
    @3
    vx
    @5
    @8
    @3
    vx
    cv
    #
    @5
    wcel
    #
    @9
    crnk
    cfv
    #
    vy
    cv
    #
    wcel
    #
    vx
    @4
    wral
    #
    @9
    @12
    wcel
    #
    wi
    #
    vy
    con0
    wral
    #
    @9
    @8
    wcel
    #
    @3
    @10
    @9
    @14
    vy
    con0
    crab
    cint
    #
    wcel
    @17
    @3
    @5
    @19
    @9
    @3
    @4
    @0
    wcel
    #
    @5
    @19
    wceq
    cA
    cB
    unwf
    #
    vy
    vx
    @4
    rankval3b
    sylbi
    eleq2d
    @14
    vy
    @9
    con0
    vx
    vex
    elintrab
    syl6bb
    @3
    @11
    @8
    wcel
    #
    vx
    @4
    wral
    #
    @17
    @18
    @3
    @22
    vx
    @4
    @9
    @4
    wcel
    @9
    cA
    wcel
    #
    @9
    cB
    wcel
    #
    wo
    @3
    @22
    @9
    cA
    cB
    elun
    @1
    @24
    @22
    @2
    @25
    @1
    @24
    @11
    @6
    wcel
    @22
    @9
    cA
    rankelb
    @11
    @6
    @7
    elun1
    syl6
    @2
    @25
    @11
    @7
    wcel
    @22
    @9
    cB
    rankelb
    @11
    @7
    @6
    elun2
    syl6
    jaao
    syl5bi
    ralrimiv
    @8
    con0
    wcel
    @17
    @23
    @18
    wi
    #
    wi
    @6
    @7
    cA
    rankon
    cB
    rankon
    onun2i
    @16
    @26
    vy
    @8
    con0
    @12
    @8
    wceq
    #
    @14
    @23
    @15
    @18
    @27
    @13
    @22
    vx
    @4
    @12
    @8
    @11
    eleq2
    ralbidv
    @12
    @8
    @9
    eleq2
    imbi12d
    rspcv
    ax-mp
    syl5com
    sylbid
    ssrdv
    @3
    @20
    @8
    @5
    wss
    @21
    @20
    @6
    @7
    @5
    @20
    cA
    @4
    wss
    @6
    @5
    wss
    cA
    cB
    ssun1
    cA
    @4
    rankssb
    mpi
    @20
    cB
    @4
    wss
    @7
    @5
    wss
    cB
    cA
    ssun2
    cB
    @4
    rankssb
    mpi
    unssd
    sylbi
    eqssd
end
