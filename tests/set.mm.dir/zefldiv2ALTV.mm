include "ceven.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cz.mm"
include "cfl.mm"
include "cfv.mm"
include "wceq.mm"
include "evendiv2z.mm"
include "flid.mm"
include "syl.mm"

theorem zefldiv2ALTV
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. Even -> ( |_ ` ( N / 2 ) ) = ( N / 2 ) )

  proof
    cN
    ceven
    wcel
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
    evendiv2z
    @0
    flid
    syl
end
