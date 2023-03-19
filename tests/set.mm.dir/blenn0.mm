include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cblen.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "c2.mm"
include "cabs.mm"
include "clogb.mm"
include "co.mm"
include "cfl.mm"
include "caddc.mm"
include "cif.mm"
include "blenval.mm"
include "ifnefalse.mm"
include "sylan9eq.mm"

theorem blenn0
  let cN: class N
  let cV: class V
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. V /\ N =/= 0 ) -> ( #b ` N ) = ( ( |_ ` ( 2 logb ( abs ` N ) ) ) + 1 ) )

  proof
    cN
    cV
    wcel
    cN
    cc0
    wne
    cN
    cblen
    cfv
    cN
    cc0
    wceq
    c1
    c2
    cN
    cabs
    cfv
    clogb
    co
    cfl
    cfv
    c1
    caddc
    co
    #
    cif
    @0
    cN
    cV
    blenval
    cN
    cc0
    c1
    @0
    ifnefalse
    sylan9eq
end
