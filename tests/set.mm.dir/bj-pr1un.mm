include "c0.mm"
include "cun.mm"
include "bj-cproj.mm"
include "bj-cpr1.mm"
include "bj-projun.mm"
include "df-bj-pr1.mm"
include "uneq12i.mm"
include "3eqtr4i.mm"

theorem bj-pr1un
  let cA: class A
  let cB: class B


  assert |- pr1 ( A u. B ) = ( pr1 A u. pr1 B )

  proof
    c0
    cA
    cB
    cun
    #
    bj-cproj
    c0
    cA
    bj-cproj
    #
    c0
    cB
    bj-cproj
    #
    cun
    @0
    bj-cpr1
    cA
    bj-cpr1
    #
    cB
    bj-cpr1
    #
    cun
    c0
    cA
    cB
    bj-projun
    @0
    df-bj-pr1
    @3
    @1
    @4
    @2
    cA
    df-bj-pr1
    cB
    df-bj-pr1
    uneq12i
    3eqtr4i
end
