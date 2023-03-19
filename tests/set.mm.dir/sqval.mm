include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmul.mm"
include "caddc.mm"
include "df-2.mm"
include "oveq2i.mm"
include "cn0.mm"
include "wceq.mm"
include "1nn0.mm"
include "expp1.mm"
include "mpan2.mm"
include "syl5eq.mm"
include "exp1.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem sqval
  let cA: class A


  assert |- ( A e. CC -> ( A ^ 2 ) = ( A x. A ) )

  proof
    cA
    cc
    wcel
    #
    cA
    c2
    cexp
    co
    #
    cA
    c1
    cexp
    co
    #
    cA
    cmul
    co
    #
    cA
    cA
    cmul
    co
    @0
    @1
    cA
    c1
    c1
    caddc
    co
    #
    cexp
    co
    #
    @3
    c2
    @4
    cA
    cexp
    df-2
    oveq2i
    @0
    c1
    cn0
    wcel
    @5
    @3
    wceq
    1nn0
    cA
    c1
    expp1
    mpan2
    syl5eq
    @0
    @2
    cA
    cA
    cmul
    cA
    exp1
    oveq1d
    eqtrd
end
