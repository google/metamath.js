include "wss.mm"
include "cdif.mm"
include "cin.mm"
include "cun.mm"
include "incom.mm"
include "wceq.mm"
include "sseqin2.mm"
include "biimpi.mm"
include "syl5reqr.mm"
include "difeq1d.mm"
include "difundi.mm"
include "dfss4.mm"
include "ineq1d.mm"
include "syl5eq.mm"
include "indif2.mm"
include "syl6eq.mm"
include "eqtr4d.mm"

theorem difuncomp
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A C_ C -> ( A \ B ) = ( C \ ( ( C \ A ) u. B ) ) )

  proof
    cA
    cC
    wss
    #
    cA
    cB
    cdif
    cA
    cC
    cin
    #
    cB
    cdif
    #
    cC
    cC
    cA
    cdif
    #
    cB
    cun
    cdif
    #
    @0
    cA
    @1
    cB
    @0
    @1
    cC
    cA
    cin
    #
    cA
    cC
    cA
    incom
    @0
    @5
    cA
    wceq
    cA
    cC
    sseqin2
    biimpi
    syl5reqr
    difeq1d
    @0
    @4
    cA
    cC
    cB
    cdif
    #
    cin
    #
    @2
    @0
    @4
    cC
    @3
    cdif
    #
    @6
    cin
    @7
    cC
    @3
    cB
    difundi
    @0
    @8
    cA
    @6
    @0
    @8
    cA
    wceq
    cA
    cC
    dfss4
    biimpi
    ineq1d
    syl5eq
    cA
    cC
    cB
    indif2
    syl6eq
    eqtr4d
end
