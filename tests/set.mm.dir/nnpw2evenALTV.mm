include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cz.mm"
include "cdvds.mm"
include "wbr.mm"
include "ceven.mm"
include "cn0.mm"
include "2z.mm"
include "nnnn0.mm"
include "zexpcl.mm"
include "sylancr.mm"
include "iddvdsexp.mm"
include "mpan.mm"
include "iseven2.mm"
include "sylanbrc.mm"

theorem nnpw2evenALTV
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. NN -> ( 2 ^ N ) e. Even )

  proof
    cN
    cn
    wcel
    #
    c2
    cN
    cexp
    co
    #
    cz
    wcel
    #
    c2
    @1
    cdvds
    wbr
    #
    @1
    ceven
    wcel
    @0
    c2
    cz
    wcel
    #
    cN
    cn0
    wcel
    @2
    2z
    cN
    nnnn0
    c2
    cN
    zexpcl
    sylancr
    @4
    @0
    @3
    2z
    c2
    cN
    iddvdsexp
    mpan
    @1
    iseven2
    sylanbrc
end
