include "cst.mm"
include "wcel.mm"
include "cin.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "stm1i.mm"
include "stm1ri.mm"
include "jcad.mm"
include "oveq12.mm"
include "df-2.mm"
include "syl6eqr.mm"
include "syl6.mm"

theorem stm1addi
  let cA: class A
  let cB: class B
  let cS: class S
  assume stle.1: |- A e. CH
  assume stle.2: |- B e. CH


  assert |- ( S e. States -> ( ( S ` ( A i^i B ) ) = 1 -> ( ( S ` A ) + ( S ` B ) ) = 2 ) )

  proof
    cS
    cst
    wcel
    #
    cA
    cB
    cin
    cS
    cfv
    c1
    wceq
    #
    cA
    cS
    cfv
    #
    c1
    wceq
    #
    cB
    cS
    cfv
    #
    c1
    wceq
    #
    wa
    #
    @2
    @4
    caddc
    co
    #
    c2
    wceq
    @0
    @1
    @3
    @5
    cA
    cB
    cS
    stle.1
    stle.2
    stm1i
    cA
    cB
    cS
    stle.1
    stle.2
    stm1ri
    jcad
    @6
    @7
    c1
    c1
    caddc
    co
    c2
    @2
    c1
    @4
    c1
    caddc
    oveq12
    df-2
    syl6eqr
    syl6
end
