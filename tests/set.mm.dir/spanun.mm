include "chil.mm"
include "wss.mm"
include "cun.mm"
include "cspn.mm"
include "cfv.mm"
include "cph.mm"
include "co.mm"
include "wceq.mm"
include "cif.mm"
include "uneq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "uneq2.mm"
include "oveq2d.mm"
include "sseq1.mm"
include "ssid.mm"
include "elimhyp.mm"
include "spanuni.mm"
include "dedth2h.mm"

theorem spanun
  let cA: class A
  let cB: class B


  assert |- ( ( A C_ ~H /\ B C_ ~H ) -> ( span ` ( A u. B ) ) = ( ( span ` A ) +H ( span ` B ) ) )

  proof
    cA
    chil
    wss
    #
    cB
    chil
    wss
    #
    cA
    cB
    cun
    #
    cspn
    cfv
    #
    cA
    cspn
    cfv
    #
    cB
    cspn
    cfv
    #
    cph
    co
    #
    wceq
    @0
    cA
    chil
    cif
    #
    cB
    cun
    #
    cspn
    cfv
    #
    @7
    cspn
    cfv
    #
    @5
    cph
    co
    #
    wceq
    @7
    @1
    cB
    chil
    cif
    #
    cun
    #
    cspn
    cfv
    #
    @10
    @12
    cspn
    cfv
    #
    cph
    co
    #
    wceq
    cA
    cB
    chil
    chil
    cA
    @7
    wceq
    #
    @3
    @9
    @6
    @11
    @17
    @2
    @8
    cspn
    cA
    @7
    cB
    uneq1
    fveq2d
    @17
    @4
    @10
    @5
    cph
    cA
    @7
    cspn
    fveq2
    oveq1d
    eqeq12d
    cB
    @12
    wceq
    #
    @9
    @14
    @11
    @16
    @18
    @8
    @13
    cspn
    cB
    @12
    @7
    uneq2
    fveq2d
    @18
    @5
    @15
    @10
    cph
    cB
    @12
    cspn
    fveq2
    oveq2d
    eqeq12d
    @7
    @12
    @0
    @7
    chil
    wss
    chil
    chil
    wss
    #
    cA
    chil
    cA
    @7
    chil
    sseq1
    chil
    @7
    chil
    sseq1
    chil
    ssid
    #
    elimhyp
    @1
    @12
    chil
    wss
    @19
    cB
    chil
    cB
    @12
    chil
    sseq1
    chil
    @12
    chil
    sseq1
    @20
    elimhyp
    spanuni
    dedth2h
end
