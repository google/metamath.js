include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "wceq.mm"
include "1e2m1.mm"
include "a1i.mm"
include "oveq2d.mm"
include "cn.mm"
include "2nn.mm"
include "uzsubsubfz1.mm"
include "mpan.mm"
include "eqeltrd.mm"

theorem ige2m1fz1
  let cN: class N


  assert |- ( N e. ( ZZ>= ` 2 ) -> ( N - 1 ) e. ( 1 ... N ) )

  proof
    cN
    c2
    cuz
    cfv
    wcel
    #
    cN
    c1
    cmin
    co
    cN
    c2
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
    c1
    @1
    cN
    cmin
    c1
    @1
    wceq
    @0
    1e2m1
    a1i
    oveq2d
    c2
    cn
    wcel
    @0
    @2
    @3
    wcel
    2nn
    c2
    cN
    uzsubsubfz1
    mpan
    eqeltrd
end
