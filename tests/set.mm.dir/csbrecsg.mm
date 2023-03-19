include "wcel.mm"
include "con0.mm"
include "cep.mm"
include "cwrecs.mm"
include "csb.mm"
include "crecs.mm"
include "csbwrecsg.mm"
include "wceq.mm"
include "csbconstg.mm"
include "wrecseq1.mm"
include "syl.mm"
include "wrecseq2.mm"
include "3eqtrd.mm"
include "df-recs.mm"
include "csbeq2i.mm"
include "3eqtr4g.mm"

theorem csbrecsg
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cV: class V


  assert |- ( A e. V -> [_ A / x ]_ recs ( F ) = recs ( [_ A / x ]_ F ) )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    con0
    cep
    cF
    cwrecs
    #
    csb
    #
    con0
    cep
    vx
    cA
    cF
    csb
    #
    cwrecs
    #
    vx
    cA
    cF
    crecs
    #
    csb
    @3
    crecs
    @0
    @2
    vx
    cA
    con0
    csb
    #
    vx
    cA
    cep
    csb
    #
    @3
    cwrecs
    #
    @6
    cep
    @3
    cwrecs
    #
    @4
    vx
    cA
    con0
    cep
    cF
    cV
    csbwrecsg
    @0
    @7
    cep
    wceq
    @8
    @9
    wceq
    vx
    cA
    cep
    cV
    csbconstg
    @6
    @7
    cep
    @3
    wrecseq1
    syl
    @0
    @6
    con0
    wceq
    @9
    @4
    wceq
    vx
    cA
    con0
    cV
    csbconstg
    @6
    con0
    cep
    @3
    wrecseq2
    syl
    3eqtrd
    vx
    cA
    @5
    @1
    cF
    df-recs
    csbeq2i
    @3
    df-recs
    3eqtr4g
end
