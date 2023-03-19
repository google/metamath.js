include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "cpellfund.mm"
include "csqrt.mm"
include "caddc.mm"
include "crp.mm"
include "rmspecfund.mm"
include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "rmspecnonsq.mm"
include "pellfundrp.mm"
include "syl.mm"
include "eqeltrrd.mm"

theorem rmbaserp
  let cA: class A


  assert |- ( A e. ( ZZ>= ` 2 ) -> ( A + ( sqrt ` ( ( A ^ 2 ) - 1 ) ) ) e. RR+ )

  proof
    cA
    c2
    cuz
    cfv
    wcel
    #
    cA
    c2
    cexp
    co
    c1
    cmin
    co
    #
    cpellfund
    cfv
    #
    cA
    @1
    csqrt
    cfv
    caddc
    co
    crp
    cA
    rmspecfund
    @0
    @1
    cn
    csquarenn
    cdif
    wcel
    @2
    crp
    wcel
    cA
    rmspecnonsq
    @1
    pellfundrp
    syl
    eqeltrrd
end
