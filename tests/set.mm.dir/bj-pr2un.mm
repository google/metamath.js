include "c1o.mm"
include "cun.mm"
include "bj-cproj.mm"
include "bj-cpr2.mm"
include "bj-projun.mm"
include "df-bj-pr2.mm"
include "uneq12i.mm"
include "3eqtr4i.mm"

theorem bj-pr2un
  let cA: class A
  let cB: class B


  assert |- pr2 ( A u. B ) = ( pr2 A u. pr2 B )

  proof
    c1o
    cA
    cB
    cun
    #
    bj-cproj
    c1o
    cA
    bj-cproj
    #
    c1o
    cB
    bj-cproj
    #
    cun
    @0
    bj-cpr2
    cA
    bj-cpr2
    #
    cB
    bj-cpr2
    #
    cun
    c1o
    cA
    cB
    bj-projun
    @0
    df-bj-pr2
    @3
    @1
    @4
    @2
    cA
    df-bj-pr2
    cB
    df-bj-pr2
    uneq12i
    3eqtr4i
end
