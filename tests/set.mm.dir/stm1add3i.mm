include "cst.mm"
include "wcel.mm"
include "cin.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "wa.mm"
include "c3.mm"
include "chincli.mm"
include "stm1i.mm"
include "stm1addi.mm"
include "syld.mm"
include "stm1ri.mm"
include "jcad.mm"
include "oveq12.mm"
include "df-3.mm"
include "syl6eqr.mm"
include "syl6.mm"

theorem stm1add3i
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  assume stle.1: |- A e. CH
  assume stle.2: |- B e. CH
  assume stm1add3.3: |- C e. CH


  assert |- ( S e. States -> ( ( S ` ( ( A i^i B ) i^i C ) ) = 1 -> ( ( ( S ` A ) + ( S ` B ) ) + ( S ` C ) ) = 3 ) )

  proof
    cS
    cst
    wcel
    #
    cA
    cB
    cin
    #
    cC
    cin
    cS
    cfv
    c1
    wceq
    #
    cA
    cS
    cfv
    cB
    cS
    cfv
    caddc
    co
    #
    c2
    wceq
    #
    cC
    cS
    cfv
    #
    c1
    wceq
    #
    wa
    #
    @3
    @5
    caddc
    co
    #
    c3
    wceq
    @0
    @2
    @4
    @6
    @0
    @2
    @1
    cS
    cfv
    c1
    wceq
    @4
    @1
    cC
    cS
    cA
    cB
    stle.1
    stle.2
    chincli
    #
    stm1add3.3
    stm1i
    cA
    cB
    cS
    stle.1
    stle.2
    stm1addi
    syld
    @1
    cC
    cS
    @9
    stm1add3.3
    stm1ri
    jcad
    @7
    @8
    c2
    c1
    caddc
    co
    c3
    @3
    c2
    @5
    c1
    caddc
    oveq12
    df-3
    syl6eqr
    syl6
end
