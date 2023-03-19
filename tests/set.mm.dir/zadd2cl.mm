include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "id.mm"
include "2z.mm"
include "a1i.mm"
include "zaddcld.mm"

theorem zadd2cl
  let cN: class N


  assert |- ( N e. ZZ -> ( N + 2 ) e. ZZ )

  proof
    cN
    cz
    wcel
    #
    cN
    c2
    @0
    id
    c2
    cz
    wcel
    @0
    2z
    a1i
    zaddcld
end
