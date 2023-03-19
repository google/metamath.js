include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cz.mm"
include "wcel.mm"
include "cfl.mm"
include "cfv.mm"
include "wceq.mm"
include "flid.mm"
include "adantl.mm"

theorem zefldiv2
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. ZZ /\ ( N / 2 ) e. ZZ ) -> ( |_ ` ( N / 2 ) ) = ( N / 2 ) )

  proof
    cN
    c2
    cdiv
    co
    #
    cz
    wcel
    @0
    cfl
    cfv
    @0
    wceq
    cN
    cz
    wcel
    @0
    flid
    adantl
end
