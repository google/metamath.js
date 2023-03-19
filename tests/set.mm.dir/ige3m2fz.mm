include "c3.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c2.mm"
include "cmin.mm"
include "co.mm"
include "c1.mm"
include "cfz.mm"
include "wceq.mm"
include "3m1e2.mm"
include "eqcomi.mm"
include "a1i.mm"
include "oveq2d.mm"
include "cn.mm"
include "3nn.mm"
include "uzsubsubfz1.mm"
include "mpan.mm"
include "eqeltrd.mm"

theorem ige3m2fz
  let cN: class N


  assert |- ( N e. ( ZZ>= ` 3 ) -> ( N - 2 ) e. ( 1 ... N ) )

  proof
    cN
    c3
    cuz
    cfv
    wcel
    #
    cN
    c2
    cmin
    co
    cN
    c3
    c1
    cmin
    co
    #
    cmin
    co
    #
    c1
    cN
    cfz
    co
    #
    @0
    c2
    @1
    cN
    cmin
    c2
    @1
    wceq
    @0
    @1
    c2
    3m1e2
    eqcomi
    a1i
    oveq2d
    c3
    cn
    wcel
    @0
    @2
    @3
    wcel
    3nn
    c3
    cN
    uzsubsubfz1
    mpan
    eqeltrd
end
