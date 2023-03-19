include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "csn.mm"
include "cun.mm"
include "df-pr.mm"
include "snwf.mm"
include "unwf.mm"
include "biimpi.mm"
include "syl2an.mm"
include "syl5eqel.mm"

theorem prwf
  let cA: class A
  let cB: class B


  assert |- ( ( A e. U. ( R1 " On ) /\ B e. U. ( R1 " On ) ) -> { A , B } e. U. ( R1 " On ) )

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
    cA
    cB
    cpr
    cA
    csn
    #
    cB
    csn
    #
    cun
    #
    @0
    cA
    cB
    df-pr
    @1
    @3
    @0
    wcel
    #
    @4
    @0
    wcel
    #
    @5
    @0
    wcel
    #
    @2
    cA
    snwf
    cB
    snwf
    @6
    @7
    wa
    @8
    @3
    @4
    unwf
    biimpi
    syl2an
    syl5eqel
end
