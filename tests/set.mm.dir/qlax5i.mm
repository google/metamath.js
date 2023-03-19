include "cort.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "chdmj2i.mm"
include "oveq2i.mm"
include "choccli.mm"
include "chabs1i.mm"
include "eqtri.mm"

theorem qlax5i
  let cA: class A
  let cB: class B
  assume qlax.1: |- A e. CH
  assume qlax.2: |- B e. CH


  assert |- ( A vH ( _|_ ` ( ( _|_ ` A ) vH B ) ) ) = A

  proof
    cA
    cA
    cort
    cfv
    cB
    chj
    co
    cort
    cfv
    #
    chj
    co
    cA
    cA
    cB
    cort
    cfv
    #
    cin
    #
    chj
    co
    cA
    @0
    @2
    cA
    chj
    cA
    cB
    qlax.1
    qlax.2
    chdmj2i
    oveq2i
    cA
    @1
    qlax.1
    cB
    qlax.2
    choccli
    chabs1i
    eqtri
end
