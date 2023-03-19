include "wfun.mm"
include "crn.mm"
include "wss.mm"
include "wa.mm"
include "ccnv.mm"
include "cin.mm"
include "cima.mm"
include "inass.mm"
include "wceq.mm"
include "sseqin2.mm"
include "biimpi.mm"
include "adantl.mm"
include "ineq2d.mm"
include "syl5eq.mm"
include "imaeq2d.mm"
include "fimacnvinrn.mm"
include "adantr.mm"
include "3eqtr4rd.mm"

theorem fimacnvinrn2
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( Fun F /\ ran F C_ B ) -> ( `' F " A ) = ( `' F " ( A i^i B ) ) )

  proof
    cF
    wfun
    #
    cF
    crn
    #
    cB
    wss
    #
    wa
    #
    cF
    ccnv
    #
    cA
    cB
    cin
    #
    @1
    cin
    #
    cima
    #
    @4
    cA
    @1
    cin
    #
    cima
    #
    @4
    @5
    cima
    #
    @4
    cA
    cima
    #
    @3
    @6
    @8
    @4
    @3
    @6
    cA
    cB
    @1
    cin
    #
    cin
    @8
    cA
    cB
    @1
    inass
    @3
    @12
    @1
    cA
    @2
    @12
    @1
    wceq
    #
    @0
    @2
    @13
    @1
    cB
    sseqin2
    biimpi
    adantl
    ineq2d
    syl5eq
    imaeq2d
    @0
    @10
    @7
    wceq
    @2
    @5
    cF
    fimacnvinrn
    adantr
    @0
    @11
    @9
    wceq
    @2
    cA
    cF
    fimacnvinrn
    adantr
    3eqtr4rd
end
