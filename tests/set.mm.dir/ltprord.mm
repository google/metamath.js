include "cnp.mm"
include "wcel.mm"
include "wa.mm"
include "cltp.mm"
include "wbr.mm"
include "wpss.mm"
include "cv.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "psseq1.mm"
include "anbi12d.mm"
include "anbi2d.mm"
include "psseq2.mm"
include "df-ltp.mm"
include "brabg.mm"
include "bianabs.mm"

theorem ltprord
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. P. /\ B e. P. ) -> ( A <P B <-> A C. B ) )

  proof
    cA
    cnp
    wcel
    #
    cB
    cnp
    wcel
    #
    wa
    #
    cA
    cB
    cltp
    wbr
    cA
    cB
    wpss
    #
    vx
    cv
    #
    cnp
    wcel
    #
    vy
    cv
    #
    cnp
    wcel
    #
    wa
    #
    @4
    @6
    wpss
    #
    wa
    @0
    @7
    wa
    #
    cA
    @6
    wpss
    #
    wa
    @2
    @3
    wa
    vx
    vy
    cA
    cB
    cnp
    cnp
    cltp
    @4
    cA
    wceq
    #
    @8
    @10
    @9
    @11
    @12
    @5
    @0
    @7
    @4
    cA
    cnp
    eleq1
    anbi1d
    @4
    cA
    @6
    psseq1
    anbi12d
    @6
    cB
    wceq
    #
    @10
    @2
    @11
    @3
    @13
    @7
    @1
    @0
    @6
    cB
    cnp
    eleq1
    anbi2d
    @6
    cB
    cA
    psseq2
    anbi12d
    vx
    vy
    df-ltp
    brabg
    bianabs
end
