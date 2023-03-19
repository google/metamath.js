include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "df-2.mm"
include "oveq1i.mm"
include "1p1times.mm"
include "syl5eq.mm"

theorem 2times
  let cA: class A


  assert |- ( A e. CC -> ( 2 x. A ) = ( A + A ) )

  proof
    cA
    cc
    wcel
    c2
    cA
    cmul
    co
    c1
    c1
    caddc
    co
    #
    cA
    cmul
    co
    cA
    cA
    caddc
    co
    c2
    @0
    cA
    cmul
    df-2
    oveq1i
    cA
    1p1times
    syl5eq
end
