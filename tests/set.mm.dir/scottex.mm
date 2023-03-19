include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "crnk.mm"
include "cfv.mm"
include "wss.mm"
include "wral.mm"
include "crab.mm"
include "cvv.mm"
include "wcel.mm"
include "0ex.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "rabexg.mm"
include "syl.mm"
include "wn.mm"
include "wex.mm"
include "neq0.mm"
include "nfra1.mm"
include "nfcv.mm"
include "nfrab.mm"
include "nfel1.mm"
include "wi.mm"
include "rsp.mm"
include "com12.mm"
include "ralrimivw.mm"
include "ss2rab.mm"
include "sylibr.mm"
include "con0.mm"
include "wrex.mm"
include "rankon.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "elrab.mm"
include "simprbi.mm"
include "rgen.mm"
include "sseq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "mp2an.mm"
include "bndrank.mm"
include "ax-mp.mm"
include "ssex.mm"
include "exlimi.mm"
include "sylbi.mm"
include "pm2.61i.mm"

theorem scottex
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint A z
  disjoint A w
  assert |- { x e. A | A. y e. A ( rank ` x ) C_ ( rank ` y ) } e. _V

  proof
    cA
    c0
    wceq
    #
    vx
    cv
    #
    crnk
    cfv
    #
    vy
    cv
    #
    crnk
    cfv
    #
    wss
    #
    vy
    cA
    wral
    #
    vx
    cA
    crab
    #
    cvv
    wcel
    #
    @0
    cA
    cvv
    wcel
    #
    @8
    @0
    @9
    c0
    cvv
    wcel
    0ex
    cA
    c0
    cvv
    eleq1
    mpbiri
    @6
    vx
    cA
    cvv
    rabexg
    syl
    @0
    wn
    @3
    cA
    wcel
    #
    vy
    wex
    @8
    vy
    cA
    neq0
    @10
    @8
    vy
    vy
    @7
    cvv
    @6
    vy
    vx
    cA
    @5
    vy
    cA
    nfra1
    vy
    cA
    nfcv
    nfrab
    nfel1
    @10
    @7
    @5
    vx
    cA
    crab
    #
    wss
    #
    @8
    @10
    @6
    @5
    wi
    #
    vx
    cA
    wral
    @12
    @10
    @13
    vx
    cA
    @6
    @10
    @5
    @5
    vy
    cA
    rsp
    com12
    ralrimivw
    @6
    @5
    vx
    cA
    ss2rab
    sylibr
    @7
    @11
    vw
    cv
    #
    crnk
    cfv
    #
    vz
    cv
    #
    wss
    #
    vw
    @11
    wral
    #
    vz
    con0
    wrex
    #
    @11
    cvv
    wcel
    @4
    con0
    wcel
    @15
    @4
    wss
    #
    vw
    @11
    wral
    #
    @19
    @3
    rankon
    @20
    vw
    @11
    @14
    @11
    wcel
    @14
    cA
    wcel
    @20
    @5
    @20
    vx
    @14
    cA
    @1
    @14
    wceq
    @2
    @15
    @4
    @1
    @14
    crnk
    fveq2
    sseq1d
    elrab
    simprbi
    rgen
    @18
    @21
    vz
    @4
    con0
    @16
    @4
    wceq
    @17
    @20
    vw
    @11
    @16
    @4
    @15
    sseq2
    ralbidv
    rspcev
    mp2an
    vz
    vw
    @11
    bndrank
    ax-mp
    ssex
    syl
    exlimi
    sylbi
    pm2.61i
end
