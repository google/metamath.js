include "cnpi.mm"
include "cxp.mm"
include "wcel.mm"
include "wa.mm"
include "ceq.mm"
include "wbr.mm"
include "cerq.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cnq.mm"
include "nqercl.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "wer.mm"
include "enqer.mm"
include "a1i.mm"
include "nqerrel.mm"
include "simp3.mm"
include "ertr3d.mm"
include "ertrd.mm"
include "enqeq.mm"
include "syl3anc.mm"
include "3expia.mm"
include "adantr.mm"
include "simprr.mm"
include "breqtrd.mm"
include "ad2antrl.mm"
include "ertr4d.mm"
include "expr.mm"
include "impbid.mm"

theorem nqereq
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ( N. X. N. ) /\ B e. ( N. X. N. ) ) -> ( A ~Q B <-> ( /Q ` A ) = ( /Q ` B ) ) )

  proof
    cA
    cnpi
    cnpi
    cxp
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    cA
    cB
    ceq
    wbr
    #
    cA
    cerq
    cfv
    #
    cB
    cerq
    cfv
    #
    wceq
    #
    @1
    @2
    @3
    @6
    @1
    @2
    @3
    w3a
    #
    @4
    cnq
    wcel
    #
    @5
    cnq
    wcel
    #
    @4
    @5
    ceq
    wbr
    @6
    @1
    @2
    @8
    @3
    cA
    nqercl
    3ad2ant1
    @2
    @1
    @9
    @3
    cB
    nqercl
    3ad2ant2
    @7
    @4
    cB
    @5
    ceq
    @0
    @0
    ceq
    wer
    #
    @7
    enqer
    a1i
    #
    @7
    @4
    cA
    cB
    ceq
    @0
    @11
    @1
    @2
    cA
    @4
    ceq
    wbr
    #
    @3
    cA
    nqerrel
    #
    3ad2ant1
    @1
    @2
    @3
    simp3
    ertr3d
    @2
    @1
    cB
    @5
    ceq
    wbr
    #
    @3
    cB
    nqerrel
    #
    3ad2ant2
    ertrd
    @4
    @5
    enqeq
    syl3anc
    3expia
    @1
    @2
    @6
    @3
    @1
    @2
    @6
    wa
    #
    wa
    #
    cA
    @5
    cB
    ceq
    @0
    @10
    @17
    enqer
    a1i
    @17
    cA
    @4
    @5
    ceq
    @1
    @12
    @16
    @13
    adantr
    @1
    @2
    @6
    simprr
    breqtrd
    @2
    @14
    @1
    @6
    @15
    ad2antrl
    ertr4d
    expr
    impbid
end
